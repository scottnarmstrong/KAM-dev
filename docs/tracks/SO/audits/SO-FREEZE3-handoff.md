# SO-FREEZE3 audit request: SEAL audit of the SO freeze (Phase B), with the Phase A follow-ups

Branch `inp-sofreeze3` (off `inp` 9517d71e). Full record: [`../FREEZE.md`](../FREEZE.md).

**Write the report to exactly `docs/tracks/SO/audits/SO-FREEZE3-seal-audit.md`** (D50; the HQ meter reads that
path).

**Status.** Phase A and Phase B are complete. The 13 D40 declarations are frozen with the D47/D49 literals. The
landed code uses the frozen definitions (Q11), and all SO data modules were rebuilt and kernel-checked on top.
The three frozen theorems are sealed by `by exact KAM.Provider.SpinOrbit.<name> …` (manifest state `SEALED`).
Authority:
- D40 (2026-10-30): the freeze proposal and Q1–Q11;
- D47 (2026-10-31, 07:00 UTC): the 2.755 % band literal, rule B's tightness clause relaxed;
- D49 (2026-10-31, 07:10 UTC): the freeze approvals;
- D50 (2026-10-31, 13:50 UTC): "I approve sealing SO-2".

All are in `docs/DECISIONS.md` on `main` (D50 at line 406 of 73f729dd).

## Commits to audit

| Commit | Content | Earlier audit |
|---|---|---|
| 1e0e888c | Phase A texts: 13 frozen files, 3 empty provider stubs, 13 manifest entries, ABI hashes | identity audit 1 (codex-1): PASS WITH NOTES |
| efe936d2 | Metadata only: decision references D46/D48 → D47/D49; fail-closed `check_identity.py` (audit 1 F2); audit 1 report | none: please confirm (item 1) |
| 0ed69133 | Q11: `Model.lean`, `Barrier.lean`, `Graph/{Inverse,Rot}.lean` use the frozen definitions; `CsegSupport.lean` width fix | none: please audit (item 2) |
| the seal commit (top of the branch) | Providers; the three frozen proof bodies; manifest `DRAFT_SORRY` → `SEALED` | SEAL audit (item 3) |

## 1. Metadata change after audit 1 (decision references only)

On `main` the two 2026-10-31 decisions were renumbered (b17bf0c0), because the first one clashed with the D46 of
2026-10-30 (Route B). The band literal moved from D46 to **D47**, and the freeze approvals from D48 to **D49**.
Commit efe936d2 changes only decision references:

- In the 13 frozen files, the docstring approval paragraph `literals D46 and` / `D48). This file is frozen` now
  reads `literals D47 and` / `D49). This file is frozen`. The new text has the same length and no rewrap.
  `git diff 1e0e888c efe936d2 -- KAM/Frozen` shows exactly two changed lines per file.
- In the 13 manifest entries, the fields `approval_ref`, `source.range` and `split_policy.ruling_ref` changed,
  with recomputed full-file, prefix/suffix and closure hashes. The other 158 entries are unchanged as JSON.
- The generator, its config and the record changed.

**No declaration changed.** All ABI hashes are unchanged, and `check_identity.py` reports all 13 files identical.
This closes audit 1 F1: the date 2026-10-31 matches D47 and D49.

Audit 1 F2 is also fixed in efe936d2:
- `check_identity.py` now compares B and the window as complete files: A's wrapper with their §1.3 imports and
  declaration blocks.
- It exits 1 on any mismatch.
- The auditor's two mutations (an appended declaration, and `<` → `≤`) are now rejected with exit 1.

Since the seal, the checker reads any proof body between the proof markers as the approved `sorry`. The proof body
is the one region outside the frozen prefix and suffix.

## 2. Q11 (commit 0ed69133): the landed code uses the frozen definitions, with no duplicates

- **`KAM/SpinOrbit/Model.lean`:**
  - adds `public import KAM.Frozen.SpinOrbit.Defs.SoField`, which brings in `SoEcc … SoV`;
  - deletes its own `soEcc, soEps, soCoeffPoly, soA, soModes, soV, soField`. They were identical to the frozen
    texts (FREEZE-PROPOSAL-2 probe 3);
  - keeps the rational companions `soEccQ`, `soEpsQ`, `soAQ`, their lemmas and `soVC`.
- **`KAM/SpinOrbit/Barrier.lean`:** adds `public import KAM.Frozen.SpinOrbit.Defs.SoBarrier` and deletes the
  landed structure. Two adapter lemmas convert between the frozen written-out `invariant` field and the
  `KAM.ODE.IsInvariantSet soField Set.univ {x | x.2.1 = P x.1 x.2.2}` form used by the landed proofs:
  - `SoBarrier.isInvariantSet`;
  - `SoBarrier.invariant_of_isInvariantSet`.

  `so_confinement` uses the first. Both are plain term proofs; no statement is weakened.
- **`KAM/SpinOrbit/Graph/Inverse.lean` and `Graph/Rot.lean`:** the two `SoBarrier` constructor sites pass
  `SoBarrier.invariant_of_isInvariantSet T.soGraph_invariant`.
- **`KAM/SpinOrbit/Data/CsegSupport.lean`:** the module docstring is rewrapped to 100 columns, and four
  continuation lines are reindented from 8 to 7 spaces (whitespace inside brackets). This is SO-DATA3 lint item
  (b). No term changed.
- **Rebuild:**
  - **Overlay:** run into a *copy* of the shared overlay (`kam-data/so-freeze3/build-overlay`, 1650 data
    `.olean`). Only this worktree's two `SpinOrbit/Data` symlinks point at it, so `main`'s overlay was not
    written.
  - **Driver:** SO-DATA3's capped driver (`scripts/spin_orbit/csplit_kbuild.py`):
    - lane 1 (Lower) under the shared kernel lock at 10 GB;
    - lane 2 (Upper) under its own lock at 8 GB, gated on MemAvailable;
    - 13 big Upper modules run on the shared lock at 10 GB.
  - **Restarts:**
    - The first run was stopped between modules for the renumbering and restarted from scratch at 08:51 UTC.
    - At 10:31:58 earlyoom sent SIGTERM to `Lower.Seg.Tors.E1_1_1`, at 5.2 GB during system-wide low memory. The
      log shows no Lean error. The lower lane was restarted and rebuilt that module.
  - **Totals:** 1071 modules built, peak RSS 9.45 GB (`Upper.Seg.Gram.E01`), about 6.9 h of module time; both
    lanes DONE by 13:34 UTC. Logs: `kam-data/so-freeze3/kbuild/` (first run: `kbuild-run1/`).
  - `lake build --no-build KAM.SpinOrbit.Data.Lower.Passes KAM.SpinOrbit.Data.Upper.Passes`:
    `All targets up-to-date (5219 jobs)`.
  - Gate build of `KAM.SpinOrbit.LunarFinalR2V2`: success (5220 jobs); only the pre-existing `if_neg`
    deprecation warnings.
  - Gate build of the SpinOrbit root parts (`KAM.Root.SpinOrbit.{Top,Graph,Tests,Lock,Data.Top,Data.Lower,
    Data.Upper}`): success (5243 jobs). This confirms there is no name clash between the frozen definitions and
    the landed code.
  - Of the 60 out-of-date modules that `lake build --no-build KAM` lists, 51 import nothing in the SpinOrbit
    model, `Barrier` or the frozen SO modules. That staleness was already present in the worktree. The other 9
    are the 7 root parts and the 2 providers, all built above.

## 3. SEAL (Phase B)

**Providers** (namespace `KAM.Provider.SpinOrbit`, quarantined; only the anchors import them):

| Provider | Proof |
|---|---|
| `LunarWindow.lean`: `lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi` | `by decide +kernel` |
| `LunarBarriers.lean`: `lunar_barriers` (exactly the frozen type) | Landed `lunar_barriers_65_v2` (`KAM/SpinOrbit/LunarFinalR2V2.lean`, SO-DATA3). Its band casts `((lunarR2BandLo : ℚ) : ℝ) = 97245 / 100000` and `((lunarR2BandHi : ℚ) : ℝ) = 102755 / 100000` are rewritten by `norm_num` equalities; `rw` reaches inside the dependent `SoBarrier` type. The window ends `lunarR2PLo = lunarPLo` and `lunarR2PHi = lunarPHi` hold by `rfl`. |
| `LunarSpinConfinement.lean`: `lunar_spin_confinement q₀ p₀ φ₀ hp` (exactly the frozen type) | Landed `lunar_spin_confinement_65_v2`, with the window hypothesis transported by the same `rfl` equalities and `((lunarR2Delta : ℚ) : ℝ) = 2755 / 100000` by `norm_num`. |

The landed constants (`KAM/SpinOrbit/LunarConstsR2.lean`, ℚ) are already the frozen literals:
- `lunarR2BandLo = 97245/100000`, `lunarR2BandHi = 102755/100000`;
- `lunarR2PLo = 9934/10000`, `lunarR2PHi = 10066/10000`;
- `lunarR2Delta = 2755/100000`.

No premise is added and no helper stands in for a frozen statement. The providers use only landed theorems,
whose own audits are SO-DATA3's.

**Frozen bodies:** only the three proof regions changed, following the precedent of the Russmann seal (8b67e992):

```
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.SpinOrbit.lunar_barriers
  by exact KAM.Provider.SpinOrbit.lunar_spin_confinement q₀ p₀ φ₀ hp
  by exact KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi
```

(one per file). The manifest `state` changed from `DRAFT_SORRY` to `SEALED` for the three theorem entries; no
hash changed, since the body is outside the prefix and suffix.

## What to audit (SEAL)

1. Each frozen theorem file differs from efe936d2 only in its proof body. Each body is exactly
   `by exact KAM.Provider.SpinOrbit.<name> …`, with the frozen binders in order.
2. The three manifest entries differ only in `state`.
3. Each provider proves exactly the frozen type, from landed results, with no added premise, conclusion-shaped
   hypothesis or substitute helper. The literal equalities are correct (item 3 table).
4. Quarantine: no module other than the anchor imports a provider, and the providers do not import the anchors.
5. Q11 (item 2): the deletions in `Model.lean` and `Barrier.lean` leave one declaration per name. The adapters are
   faithful in both directions, the constructor sites are correct, and the `CsegSupport` change is whitespace only.
6. The metadata change (item 1) touches decision references only.
7. Axioms and kernel replay (below).

## Checks run (2026-10-31, after the seal)

- Gate build of `KAM.Provider.SpinOrbit.{LunarBarriers,LunarSpinConfinement,LunarWindow}`: success (5225 jobs);
  no warning in the provider files.
- Gate build of `KAM.Frozen.SpinOrbit.Theorems.{LunarBarriers,LunarSpinConfinement,LunarWindow}`: success (5228
  jobs), no `sorry` warning.
- `#print axioms` (scratch file importing the three anchors):

  ```
  'KAM.SpinOrbit.lunar_barriers' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.SpinOrbit.lunar_spin_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.SpinOrbit.lunarPLo_lt_lunarPHi' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Provider.SpinOrbit.lunar_barriers' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Provider.SpinOrbit.lunar_spin_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
  'KAM.Provider.SpinOrbit.lunarPLo_lt_lunarPHi' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- Kernel replay. Under the shared kernel lock, `systemd-run MemoryMax=10G`:

  ```
  LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose <the 13 KAM.Frozen.SpinOrbit modules>
    KAM.Provider.SpinOrbit.{LunarBarriers,LunarSpinConfinement,LunarWindow}
  ```

  Result: `replaying …` for all 16 modules, exit 0, 134 s, 3.7 GB.
- `check_frozen_anchors.py`: `FROZEN-ANCHOR GUARD OK`.
- `abi_hashes.py --check`: `ABI HASHES OK (171 frozen declarations)`.
- `check_identity.py`: `ALL IDENTICAL`, exit 0.
- `lint_sources.sh`: `check_lean_modules: PASS (3408 Lean files)`, guard OK, ABI OK. The only failure is
  `KAM.lean is out of date … (KAM/Root/Frozen.lean, KAM/Root/Provider.lean)`, the generated root that rule 10
  leaves to landing. The `CsegSupport` width errors are gone.

## Landing note

The data `.olean` of this branch live in `kam-data/so-freeze3/build-overlay`. Landing needs `main`'s
`SpinOrbit/Data` symlinks repointed there (orchestrator), plus the root regeneration.
