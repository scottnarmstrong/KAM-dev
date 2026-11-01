# LP3-SP-DRIFT handoff (spatial stopped-drift supplier, `k = n + n`)

Branch `inp-lp-lp3spdrift`. Track LP, non-frozen. No `sorry`, no heartbeat override, no existing file edited
(except generated `KAM/Root/Planetary.lean`: three import lines from `scripts/gen_root_imports.py`).
Imports the SEALED anchor only through planar `Nek.Cells`/track P `Exponential.Stopped` (D58); no provider.

## Files (460 lines total)
- `KAM/Planetary/Spatial/Nek/Drift/Kepler.lean` (168): Kepler margin on cells, cell-family threshold.
- `KAM/Planetary/Spatial/Nek/Drift/Slow.lean` (116): sharp slow bound, chart AMD, slow erosion, `V_j` solution premise.
- `KAM/Planetary/Spatial/Nek/Drift.lean` (176): main theorem.

## Declarations (namespace `KAM.Planetary.Spatial`)
Main, `Drift.lean`:
```
def spatialNekRadius (n) (B0 μ : ℝ) : ℝ := (B0 * μ) ^ planetaryDriftExponent n
def spatialNekHorizon (n) (B0 μ : ℝ) : ℝ := Real.exp ((B0 * μ) ^ (-planetaryTimeExponent n))
theorem spatial_stopped_drift_nek (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) {L} (hL : IsCompact L) (hLch : L ⊆ chamber ν)
    {δ rg} (hg : IsSharedTube ν L δ rg) (hδ : 0 < δ) :
  ∃ B0, 1 ≤ B0 ∧ ∃ μ₀, 0 < μ₀ ∧ ∀ μ, 0 < μ → μ ≤ μ₀ →
    0 < r ∧ r ≤ 4 * rg ∧ n * r + strongThresholdModulus ν (sharedTube ν L δ rg) r ≤ δ / 4 ∧
    ∀ z₀ : Phase (n * 3), spatialActionVector ν z₀ ∈ L →
      SpatialLiftData ν (sharedTube ν L δ rg) z₀ δ r →
      ∀ J, J.OrdConnected → 0 ∈ J → ∀ z, IsSpatialMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
        |t| ≤ T → (∀ u ∈ uIcc 0 t, SpatialNegativeEnergy ν (z u) ∧ ‖Λ(z u) - Λ z₀‖ < r ∧
            spatialStrongAMD ν (z u) < strongThreshold ν (Λ (z u)) - δ / 2) →
        ‖Λ(z t) - Λ z₀‖ ≤ r / 2        -- r = spatialNekRadius n B0 μ, T = spatialNekHorizon n B0 μ
theorem exists_spatialNek_rpow_lt   -- ε < κ^{1/b} → ε^b < κ
```
The last conjunct is literally the `hstop` of `spatialStrongFirstExit_of_stopped_drift` (`r := r`, `T := T`) once
`SpatialLiftData` is supplied (checked by a scratch `exact` in `.drafts/chk_hstop.lean`, which compiles). The
first three conjuncts are the `hr`, `hball` (via `r ≤ 4 r_g`) and `hbudget` inputs (the budget lemma).
`B0, μ₀` depend only on `(n, ν, L, δ, r_g)`, before `μ` and the orbit.

`Drift/Slow.lean`: `spatialNek_sharp_slow_bound` (`C(z u) < B(c) − 3δ/8` on the stopped interval),
`spatialNek_chart_amd_lt` (same for `spatialChartAMD (w u)` via alignment), `spatialNek_slow_mem_innerCore`
(`stopped_slow_erosion` at `n + n`, constant `√(2·2n)`), `spatialNek_isSolutionOn_of_region` (`V_j`-form).
`Drift/Kepler.lean`: `nekCell_nbhd_re_mem_ball`, `spatialNek_kepler_premises`, `exists_spatialNek_cell_threshold`
(one `ε₀` for a finite family of cells, two-sided drift for `h = planetaryKeplerC ν`, via `cell_drift_two_sided`
at `k = n + n`, planetary exponents).

## Approach
Plan §2.4/§2.5 steps 1–8 verbatim: SP-LIFT's `spatialChartLift_of_stopped`; cover cell with `‖Λ z₀ − c‖ < η/2`;
fast erosion from `IsNekCover.mem_innerCore`; sharp slow bound then slow erosion; `V_j` membership; frozen theorem via
CELL's `cell_drift_two_sided`; `Ψ (w u) = z u` converts chart to physical action. Thresholds: `ε = B0 μ ≤ ε*/2` with
`ε* = min(ε₀, ε₁, 1)`, `ε₁` from one `rpow` bound for `min(η/4, εD, r1, 4 r_g)`; `T = exp(ε^{-a}) ≤ ε⁻¹ exp(ε^{-a})` as `ε < 1`.

## Not done / notes
Nothing omitted from the brief. Additional typing datum in the statement: `Λ(z₀) ∈ L` (planar analogue: `hAz`);
it places the initial action in the level set (with `hd.amd` and `spatialStrongAMD ≥ 0`). Not a drift/AMD/alignment premise.

## Checks
- `lp_build.sh … KAM.Planetary.Spatial.Nek.Drift.Kepler`, `…Drift.Slow`, `…Drift` (after building the previously unbuilt
  `StrongAMD.Nek.Cells` and `StrongAMD.PlanarSafety.Constants`): `✔ Built KAM.Planetary.Spatial.Nek.Drift (14s)`,
  `Build completed successfully (9375 jobs)`; no warning from my files.
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS (3785 Lean files…)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`).
- `main_shortname_check.py … Drift Drift.Kepler Drift.Slow`: `short-name check OK`, exit 0.
- `#print axioms` (via `lp_lean.sh`, `.drafts/ax_spdrift.lean`), all eight declarations (`spatial_stopped_drift_nek`,
  `exists_spatialNek_cell_threshold`, `spatialNek_kepler_premises`, `nekCell_nbhd_re_mem_ball`,
  `spatialNek_sharp_slow_bound`, `spatialNek_chart_amd_lt`, `spatialNek_slow_mem_innerCore`,
  `spatialNek_isSolutionOn_of_region`): `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
1. `spatial_stopped_drift_nek` statement vs `hstop`: exponents are the `planetary*` names (equal to the frozen `partial*` by
   the bridges in `Exponential/Stopped.lean`, applied inside `exists_spatialNek_cell_threshold`); `μ ≤ μ₀` (non-strict) comes
   from `B0 μ ≤ ε*/2 < ε*`; `Λ(z₀) ∈ L` typing datum.
2. Kepler margin (`nekCell_nbhd_re_mem_ball`, `spatialNek_kepler_premises`): `‖Re z − c‖ < 2η + ρ = 5rs/8 < rs`, and
   `closedBall c rs ⊆ cthickening (4 r_g) 𝓛_δ` (`rs ≤ 4 r_g`); constants `g = νmin³/Imax³`, `m = 3νmin³/Imax⁴`,
   `M = keplerHessConst ν Imin`.
3. Sharp slow bound: `|B(Λ(z u)) − B(I⁰)| ≤ δ/16` by the modulus at `4 r_g` (needs `r ≤ 4 r_g`), `|B(I⁰) − B(c)| ≤ δ/16`
   by `nekCell_threshold_bound_of_close`; total `δ/2 − δ/8 = 3δ/8`.
4. Slow erosion constant `√(2·((n+n:ℕ):ℝ))` agrees with `exists_spatialNekSlowGap`; `spatialChartAMD` unfolds to the slow sum.
5. `hfield` of `spatialNek_isSolutionOn_of_region` is taken from `exists_spatialNekPerturbation`'s last two conjuncts.

## Errata / deviations / design signals
No source defects found. Deviation from the planar plan text: `kepler_cell_drift` (LP3-CELL) is NOT used, because its
collar `ρ₀ = Imin/4` is below the fixed cell widths; the plan's own margin argument is used with `cell_drift_two_sided`
(Cells.lean, unchanged). No heartbeat or size issues (all files < 180 lines, each builds in about 10 s).
