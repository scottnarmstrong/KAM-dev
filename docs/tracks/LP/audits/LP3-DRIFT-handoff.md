# LP3-DRIFT handoff (planar stopped-drift supplier in the `hstop` shape, no Diophantine premise)

Branch `inp-lp-lp3drift`, track LP, non-frozen. No `sorry`, no heartbeat override, no existing file edited
(except the generated `KAM/Root/Planetary.lean`, two import lines from `scripts/gen_root_imports.py`).
Imports the sealed anchor only through `Nek/Cells` and track P's `Exponential/Stopped` (D58); no provider.

## Files
- `KAM/Planetary/StrongAMD/Nek/Drift/Stopped.lean` (184 lines): the cellwise core.
- `KAM/Planetary/StrongAMD/Nek/Drift.lean` (189 lines): constants over the cover and the supplier.

## Declarations (namespace `KAM.Planetary.StrongAMD`)
Stopped.lean:
- `isSharedTube_of_le`: `IsSharedTube ν L δ r → 0 < r' → r' ≤ r → IsSharedTube ν L δ r'` (compactness, chamber,
  `strongThresholdModulus_mono_set` and `_mono`). Needed to put `r_g ≤ ρ₀/2` (see AUDIT FOCUS 1).
- `nek_sharp_slow_bound` (plan §2.4 step 4, the curvature step): `‖Λ z₀ − c‖ < η/2`, `c ∈ 𝓛_δ`, `Λ z₀ ∈ 𝓛_δ`,
  `r ≤ 4 r_g`, `StoppedOn` ⟹ `strongAMD ν (z u) < B(c) − 3δ/8` on `uIcc 0 t`.
- `nekNHam ν P ε := degenerateHamiltonian (realPart (planetaryKeplerC ν)) (fun _ x => (P (complexifyPhase x)).re) ε`.
- `nek_isSolutionOn_cell` (step 6, the `V_j`-form of the solution premise): lifted chart curve in `V_j` with fast
  actions in `G_j` and equal fields on `V_j` ⟹ frozen `IsSolutionOn (nekNHam ν P ε) {fast ∈ G_j} (uIcc 0 t) w`.
- `nek_stopped_drift_core` (steps 1–7): lift (`LiftData.lpChartLift_of_stopped`), dictionary
  (`lpChart_action`, `lpChart_strongAMD`), slow erosion (`stopped_slow_erosion`), fast erosion
  (`nekCell_mem_of_close`, `nekCell_mem_innerCore`), solution premise, and the cell conclusion. The cell data
  `hfield` (field identity on `V_j`) and `hcell` (frozen conclusion for the cell) are hypotheses here, discharged
  in Drift.lean; they are not source premises and the lemma is not exported as a source result.

Drift.lean:
- `exists_pos_rpow_lt`: `∃ y > 0, ∀ ε, 0 < ε → ε < y → ε ^ b < x`.
- **`lp_stopped_drift_nek`** (the supplier):
  ```
  theorem lp_stopped_drift_nek (hn : 2 ≤ n) {ν} (hν : ∀ i, 0 < ν i) {L} (hL : IsCompact L)
      (hLch : L ⊆ chamber ν) {δ} (hδ : 0 < δ) :
      ∃ rg B0 μ₀ : ℝ, IsSharedTube ν L δ rg ∧ 1 ≤ B0 ∧ 0 < μ₀ ∧
        ∀ μ, 0 < μ → μ ≤ μ₀ →
          0 < (B0*μ)^planetaryDriftExponent n ∧ (B0*μ)^planetaryDriftExponent n ≤ 4*rg ∧
          n * r + strongThresholdModulus ν (sharedTube ν L δ rg) r ≤ δ/4 ∧          -- budget lemma (r := (B0*μ)^b)
          ∀ z₀, actionVector ν z₀ ∈ strongLevelSet ν L δ →
            LiftData ν (sharedTube ν L δ rg) z₀ δ r →
            ∀ J, J.OrdConnected → 0 ∈ J → ∀ z, IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
              |t| ≤ Real.exp ((B0*μ)^(-planetaryTimeExponent n)) → StoppedOn ν z₀ δ r z t →
              ‖actionVector ν (z t) − actionVector ν z₀‖ ≤ r / 2
  ```
  with `r = (B0*μ)^planetaryDriftExponent n`. Constants depend on `(n, ν, L, δ)` only (before `μ` and the orbit).
- **`lp_stopped_drift_nek_hstop`**: the same with `∃ rg B0 c T₀ μ₀`, `T₀ = 1`, `c = B0^(-a_n)`, time
  `T₀ * exp (c * μ^(-planetaryTimeExponent n))` (LP1's shape), and the stopped condition unfolded: its last
  hypothesis is literally the antecedent of `hstop` in `strongFirstExit_of_stopped_drift` with `r := (B0*μ)^b_n`,
  so LP3-PS can match `hstop` by `exact`. Assembly constant: `AΛ := B0^b_n / 2`.

## Items NOT done
None omitted. The assembly (`strongFirstExit_of_stopped_drift` call, LiftData construction from `r ≤ r₁`, `r ≤ 4 r_g`) is LP3-PS.
The budget lemma is a conjunct of the supplier (it is `exists_budget_radius` for `r < r₁`; no separate declaration).

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-lp3drift KAM.Planetary.StrongAMD.Nek.Drift.Stopped KAM.Planetary.StrongAMD.Nek.Drift`:
  `✔ Built …Drift.Stopped`, `Build completed successfully (9345 jobs)`; no warning from either file
  (checked with `lp_lean.sh`: empty output).
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`); a first run caught a
  101-character docstring line, fixed.
- `main_shortname_check.py … Nek.Drift Nek.Drift.Stopped`: `short-name check OK`, exit 0.
- `#print axioms` (scratch `.drafts/ax_drift.lean` through `lp_lean.sh`): `lp_stopped_drift_nek`,
  `lp_stopped_drift_nek_hstop`, `nek_stopped_drift_core`, `nek_sharp_slow_bound`, `nek_isSolutionOn_cell`,
  `isSharedTube_of_le`: all `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
1. **Order of choices (Drift.lean).** `kepler_cell_drift` needs `G'_j ⊆ cthickening ρ₀ U` and `ρ ≤ ρ₀` with `ρ₀`
   depending on the compact set `U`. It is applied with `U := 𝓛_δ` (not the shared tube, whose minimal coordinate may be
   tiny), so `ρ₀ = ρ₀(ν, 𝓛_δ)` precedes everything; then `rg := min rg₀ (ρ₀/2)` (shared tube shrunk by
   `isSharedTube_of_le`), then `R, B0, P` (from `exists_nekPerturbation` for this `rg`), then the cover. With
   `η ≤ r_g` and `ρ = η/2` this gives `G'_j = ball(c_j, 2η) ⊆ cthickening ρ₀ 𝓛_δ` and `ρ ≤ ρ₀`. Check there is no cycle.
2. **Threshold bookkeeping.** `ε₀ = min 1 (min μ₁ (min y1 (min y2 y3)))` with `y1,y2,y3` from `exists_pos_rpow_lt` for
   `η/4`, `ε_D`, `r₁`; `μ₀ = ε₀/(2 B0)` so `ε = B0 μ ≤ ε₀/2 < ε₀` (strict, as the frozen theorem needs `μ < μ₀`).
   `ε < 1` gives `exp(ε^{-a}) ≤ ε⁻¹ exp(ε^{-a})` (the frozen horizon).
3. **Quantifier order and typing datum.** Premise `actionVector ν z₀ ∈ strongLevelSet ν L δ` is typing data (LiftData does
   not state membership in `L`; LP1's assembly derives it from the axis in `A`). No drift, AMD or confinement premise is
   assumed; `LiftData` and `StoppedOn` are the sealed LP-LIFT interface.
4. **`nek_sharp_slow_bound`:** constants `δ/16 + δ/16 − δ/2 = −3δ/8`, with `‖Λ(z u) − I⁰‖ < r ≤ 4 r_g` for the shared
   modulus and `‖I⁰ − c‖ < η/2` for the cell bound (`nekCell_threshold_bound_of_close`).
5. **Exponent bridge.** The statements use `planetary*Exponent`; the proof rewrites with
   `planetary{Drift,Time}Exponent_eq_partial` before applying CELL (stated with `partial*`).
6. **`nek_stopped_drift_core`:** `hcell` is applied on `uIcc 0 t` (two-sided, as `cell_drift_two_sided`), including
   `t < 0` and `t = 0`; `hfield` comes from `exists_nekPerturbation` components 3 and 4 (`B0 * μ` parameter).

## Source defects, deviations, design signals
- No source defects found. Plan §2.4 step 5 uses `A₁ := A_j′`; implemented exactly (`exists_nekSlowGap`).
- Deviation (plan §2.3 said the Kepler data were taken from `U` the shared tube): `U := 𝓛_δ` for `ρ₀`, plus the shrink of
  `rg` (above), because `kepler_cell_drift` (LP3-CELL) requires `ρ ≤ ρ₀(U)`. No change to any existing file.
- Statement uses `μ ≤ μ₀` (LP convention); internally `μ_frozen = B0 μ < ε₀`.
- Design signals: none. Both files build in ~10 s at default heartbeats; 184 and 189 lines.
