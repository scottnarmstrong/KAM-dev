# Handoff HD11964-COVER-LEAN (phase 2: the cover lemma landed in the application package)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (2 November 2026, after the reboot):
- land `Cover.lean` (the 50-cell fitted cover) with narrower imports; one logged 5 GB solo build is allowed if the
  build still exceeds 4 GB;
- check the cell format against kamx-hd-layer's handoff (branch `hd-layer`);
- one Lean process at a time under 4 GB, 20 GB anon gate.

Nothing pushed.

**Status: done.**
- `HD11964.Cover` and `HD11964.CoverPlan` are built and imported by the package root `HD11964`.
- `HD11964.Cover.fitPlan_covers : CoversReps fitPlan.cells (1/500)` holds for the 50-cell fitted cover.
- Every build stayed under the 4 GB cap; the 5 GB fallback was not used.

## Files

| file | change |
|---|---|
| `applications/hd11964/HD11964.lean` | imports `HD11964.Cover` and `HD11964.CoverPlan`; docstring |
| `applications/hd11964/HD11964/Cover.lean` | status lines of the docstring replaced; code unchanged since `c3b04dc3` |
| `applications/hd11964/HD11964/CoverPlan.lean` | status lines of the docstring removed; code unchanged |

No core file changed. The landed `HD11964/NoCrossing.lean` and `HD11964/Threshold.lean` are untouched.

## Narrower imports: measured, and not worth it

Each probe below is a module with one import and `example : True := trivial`, run as `lake env lean` under the
4 GB cap. Max RSS:

| import | max RSS | wall |
|---|---:|---:|
| `Mathlib` | 3,415,548 KB | 9.8 s |
| `KAM.Planetary.Exponential.Setting` (`chartAMD`, `chartSafe`) | 3,603,892 KB | 2.7 s |
| `KAM.Application.LambdaDrift.Rotation` (`chartRot`) | 3,607,332 KB | 2.7 s |
| `HD11964.Threshold` (`lamLo`, `lamHi`, `cBar`) | 3,605,456 KB | 2.7 s |
| `HD11964.NoCrossing` (`region`; the current import) | 3,611,828 KB | 2.7 s |

- Every `KAM` module has `public import Mathlib`. The floor is all of Mathlib, and the LP lane adds only about
  0.2 GB.
- Moving `region` into a lighter module (the plan of the COVERLEMMA resume notes) would save about 8 MB, at the cost
  of editing the landed `NoCrossing.lean`. Not done.
- `Cover.lean` keeps `public import HD11964.NoCrossing`, and its docstring says why.
- Max RSS overstates the cgroup charge, because it counts shared memory-mapped `.olean` pages. A non-module
  `import HD11964` check showed 6.96 GB max RSS inside the 4 GB scope without being killed. So the "4.15 GB, 43 MB
  under the cap" of HD11964-COVERLEMMA (a `lake env lean` max RSS) overstated the risk.

## Builds (one process each, `MemoryMax=4G`, `MemorySwapMax=0`, `nice -n 5`)

| target | result | Lean time | wall | max RSS |
|---|---|---:|---:|---:|
| `lake build --no-build HD11964.Cover` (dry run) | only `HD11964.Cover` out of date (9365 jobs) | | | |
| `lake build HD11964.Cover` | built, no warnings in the file | 6.4 s | 8.4 s | 3,195,092 KB |
| `lake build HD11964.CoverPlan` (includes the `decide +kernel` of the plan) | built, no warnings | 3.5 s | 5.6 s | 3,174,200 KB |
| `lake build HD11964` (root) | built (9368 jobs) | 1.9 s | 4.0 s | 2,965,228 KB |

User anon was at most 1.2 GB before each build.

These are the second builds, after the docstring change; the first builds of the same code took 6.3 s and 3.5 s.

**After the reboot**, this shell had no `XDG_RUNTIME_DIR`, so `systemd-run --user` failed ("Failed to connect to
bus") before Lean ran. Every capped command now starts with
`export XDG_RUNTIME_DIR=/run/user/1004 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1004/bus`.

## Checks

- **Axioms** (module file `public import HD11964`, `#print axioms`). Each of the following depends on
  `[propext, Classical.choice, Quot.sound]` only:
  - `coversReps_of_ok`, `fitPlan_covers`;
  - `hRS_of_coversReps`, `existsRep`;
  - `AffineCell.map_eq_cellMap`, `mem_toSet_of_memIneq`;
  - `memOfWedge`, `memOfDisc`.
- **Statements** (`#check`):
  - `fitPlan_covers : CoversReps fitPlan.cells ↑(1/500)`;
  - `coversReps_of_ok : CoverTheorem` (`∀ P, P.ok = true → CoversReps P.cells P.d`).
- **`scripts/lint_sources.sh`.**
  - `check_lean_modules` PASS (4429 files), the anchor guard OK, lines ≤ 100, no forbidden token.
  - The only failure is the known environmental ABI-hash step: `KAM/Frozen/Planetary/Spatial/Defs/
    AngularMomentum3.olean` is missing in this worktree's `.lake`.
- **Hygiene.** No heartbeat options, no `native_decide`. `Cover.lean` has 675 lines and `CoverPlan.lean` 279.

## The cell format against kamx-hd-layer (branch `hd-layer` at `71c78fcc`)

The branch is unchanged since my 04:00 check (last commit 02:48 UTC). The comparison in HD11964-COVERLEMMA stands.

**Matching:**
- the variable order `(Λ_c, Λ_b, ξ_c, η_c, ξ_b, η_b)`;
- the LP-chart slow variables `ξ = slow w.1`, `η = slow w.2`;
- every angle in a cell, `|u_j| ≤ 1`, and rational centres;
- the rotation convention. `tf_cell.py --rot_b=cs,sn` gives `ξ_b = ξ0 + h₁ cs u₁ − h₂ sn u₂` and
  `η_b = η0 + h₁ sn u₁ + h₂ cs u₂`, which is `AffineCell.map` with `(cs, sn) = (a, b)`.

**Differences**, all of representation or to-do, none of convention:
1. **Matrix and field.** Their `cellMap c Mx u` uses a general `Mx : Fin d → Fin d → ℚ` over `ℂ`.
   - The landed adapter is `AffineCell.toMx` with `map_eq_cellMap : k.map u = fun i => c i + Σ_j toMx i j · u j`
     (over `ℝ`).
   - The `ℂ` cast `cellMap k.c k.toMx (ofReal ∘ u) = ofReal ∘ k.map u` is a two-line `push_cast` lemma, once
     `PackedTF/Assembly.lean` and `HD11964` share a branch.
2. **Consumer glue.** Their `TFModel.bound_of_cell` bounds `F θ (cellMap c Mx u)`. The consumer must identify that
   with the chart function at `w`, with `θ = λ/2π` and `x = cellCoord w`. This is outside the cover lemma.
3. **Producer (my side).**
   - `prod2_hp.py` must expand `χ₁`, `χ₂` in the rotated cell variables, as `tf_cell.py --rot_b` and
     `cover2_fit.rotate` do.
   - The cell data must be the exact rationals of `fitPlan` (`validation/cover2-plan-k0.2-d2e-3.json`).

## Open items

- **`F`'s rotation invariance** (`hFrot` of `bracket_bound_of_rotation` and `range_bound_of_rotation`;
  AUDIT-HD11964-P2B-1's forward note). It is open, as ruled.
- The producer's rotated expansion (difference 3).
- The `ℂ` adapter lemma and the consumer glue (differences 1 and 2), once the cover and the layer share a branch.

## Resume

- **State.** Everything is committed on `hd11964-p2` (this handoff's commit). The scratch copies stay in
  `~/kam-data/hd11964/coverlemma/`, and this task's build logs are in `~/kam-data/hd11964/logs/`
  (`build*-HD11964*.log`).
- **To rebuild**, from `applications/hd11964`, one process at a time:

      export XDG_RUNTIME_DIR=/run/user/1004 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1004/bus
      grep '^anon ' /sys/fs/cgroup/user.slice/user-1004.slice/memory.stat          # wait while > 20 GB
      systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 5 lake build HD11964.Cover
      systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 5 lake build HD11964.CoverPlan
      systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 nice -n 5 lake build HD11964

- **Next** (for the orchestrator):
  - landing `hd11964-p2` on main (the core files of P2B follow-ups and the application package);
  - the producer's rotated expansion;
  - the consumer glue once `hd-layer` lands.

## Audit fixes (AUDIT-HD11964-COVER-1, PASS WITH CHANGES)

All three requested changes are made in `HD11964/Cover.lean`. There is no change of substance; `CoverPlan.lean` is
unchanged.
- **C1.** The module docstring now states that the step from `hRS` to the bridge's region bounds also needs `F`'s
  rotation invariance (`hFrot`, with `O` rotation-invariant and `O ⊆ chartSafe ν`, for the global `F`), and that
  this is open.
- **C2.**
  - The header "The planned lemmas (statements only)" and its `Prop` definitions are removed.
  - `MemToSetIff` is now proved, as `mem_toSet_iff`, with the new direction `memIneq_of_mem_toSet`.
  - The stale "Scratch proofs" header is replaced.
- **C3.** Every theorem is stated inline, and the theorem names are snake_case:

  | old | new |
  |---|---|
  | `existsRep : ExistsRep` | `exists_chartRot_rep` |
  | `existsSlab`, `existsSlab_aux` | `exists_slab_of_slabsChainOk`, `…_aux` |
  | `discOfRegion` | `sq_add_sq_le_of_mem_region` |
  | `existsWedge` | `exists_wedge_of_chainOk` |
  | `memOfWedge` | `memIneq_of_wedgeOk` |
  | `memOfDisc` | `memIneq_of_discOk` |
  | `coversReps_of_ok : CoverTheorem`, `hRS_of_coversReps : HRSOfCovers` | same names, statements inline |

**Checks.**
- `lake build HD11964.Cover`, `HD11964.CoverPlan` and `HD11964` succeed under the 4 GB cap, with no warnings in
  these files.
- `#check coversReps_of_ok` now prints `∀ (P : CoverPlan), P.ok = true → CoversReps P.cells ↑P.d`.
- `#print axioms` of the ten main theorems gives `[propext, Classical.choice, Quot.sound]`.
- The lint passes, except the environmental ABI-hash step.
