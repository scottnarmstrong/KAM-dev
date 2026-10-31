# W7-MEASURE handoff

Package W7-MEASURE (blueprint `blueprint-W/parts/w7-measure.tex`, `bpW:w7`), branch `inp-wpl`.
Off the frontier: source-faithful infrastructure used by several nodes; the dependency graph is still being built.
All modules are under `KAM/Wave/Measure/`, namespace `KAM.Wave`. Every blueprint label of the package is done; no
`sorry`, `axiom`, `maxHeartbeats` (or any budget override); the largest file is 413 lines.

## Files and the declarations proved, per blueprint label
| label | module | declarations |
|---|---|---|
| `freqcoords` | `Coords` | `measDA`, `measNA`, `measLA`, `measLA_eq`, `measNA_lt`, `measure_omegaTan_image`, `norm_omegaTan_sub_le`, `norm_sub_le_measLA_mul`, `omegaNor_eq`, `measS_eq`, `abs_measS_sub_le` |
| `indexdef` | `Lambda` | `normLab`, `japL`, `absWt`, `IsLam`, `IsLamMinus`, `hatW`, `kAbs`, `kAk`, `lam_cases` |
| `unpert-bounds` | `UnpertBounds` | `abs_measS_le`, `norm_omegaTan_le` (i); `three_betaStar_japL_le` (ii); `omegaNor_sub_approx` (iii); `abs_linF_omegaNor_sub_le` (iv) |
| `constdef`, `Xdef`, Xzones#consts | `Consts` | `measW`, `measTheta`, `measCLam`, `measKstar`, `measJstar`, `measXSet`, `measXSet_finite`, `measNX`, `measSigmaX(_pos/_le)`, `measCX(_pos/_le)`, `measTheta0`, `measAlpha0`, `measZ3`, `measCP`, `measCI`, `measC7`, `alphaHat`, `alphaCheck` |
| `zones`, `family` | `Family` | `MeasSetup`, `IsFreqPair` ((H1),(H2)), `AdmissibleFamily`, `zoneSet`, `prepZone`, `InZ`, `prepSet` (Ξ), `iterSet`, `exclSet` (ℰ), `isFreqPair_unpert` |
| `slab`, `ext-borel` | `Slab` | `slab_measure_le`, `volume_le_of_coord_slices`, `measurableSet_abs_lt_of_continuousOn` |
| `zone` | `Pair`, `ZoneBound` | `IsFreqPair.zone_measure_le`, `measure_abs_lt_le_of_growth`, `IsFreqPair.linF_lip`, `IsFreqPair.drift_le` |
| `sep`, `largek`, `dichotomy` | `SepLarge` | `IsFreqPair.sep`, `zoneSet_zero_empty`, `IsFreqPair.largek`, `IsFreqPair.dichotomy` |
| `Xzones` | `Xzones` | `IsFreqPair.Xzone_empty`, `IsFreqPair.Xzone_measure_le` |
| `count` | `Count`, `ZetaSum` | (i) `lamPlusFin`, `card_lamPlusFin_le`, `mem_lamPlusFin`; (ii) `tsum_Kprev_le`; (iii) `tsum_lattice_le` (with `encard_l1Sphere_le`, exact count `≤ 4N`) |
| `prep` | `ZoneSums`, `MinusZones`, `MinusSum`, `PrepMinus`, `Prep` | `IsFreqPair.plus_bound`, `IsFreqPair.X_bound`, `IsFreqPair.minus_n_bound`, `minus_assembly`, `prep_minus_n_bound`, `prepSet_measure_le` |
| `iter` | `IterMinus`, `Iter` | `iter_minus_n_bound`, `iterSet_measure_le` |
| `measurable` | `Measure` | `exclSet_measurableSet` (Ξ, ℰ_it, ℰ, Π∖ℰ) |
| `measure` | `Measure` | `exclSet_measure_le`: `MeasurableSet ℰ ∧ volume ℰ ≤ ofReal (measC7 m hm * Metric.diam Π * α^(32/47))` |
| `melnikov` | `Measure` | `melnikov_prep`, `melnikov_prep_zero`, `melnikov_iter`, `melnikov_sep` |
| `shells`, `shell-geom` | `Shells` | `shellSet`, `shellInner`, `volume_shellSet`, `shellSet_disjoint`, `boxIoo_subset_iUnion_shell`, `shellSet_norm_ge`, `shellSet_dist_le`, `volume_shell_diff_inner_le` |
| `shell-est` | `ShellEst` | `shell_defect_le` (the estimate for one `k`) |
| `density` | `Density` | `density_one_of_shells`: exactly the frozen clause (1), `Tendsto (fun h => volume (Γ ∩ ball 0 h) / volume ({I | ∀ i, 0 < I i} ∩ ball 0 h)) (𝓝[>] 0) (𝓝 1)` |
| `dioph` | `Dioph` | `isDiophantine_of_lower_bound`: `KAM.IsDiophantine (c/(4π)) 24 (fun i => ω i/(2π))` |
| `limit` | `Limit` | `tendsto_frequency_limit`: exactly the frozen `Tendsto ν (𝓝[Γ] 0) (𝓝 fun i => lam m hm (i:ℕ).succPNat / (2π))` |

## Interface for W6 and W8
* Parameters: `MeasSetup m hm Π α` (Π Borel in the ball `‖ξ‖ ≤ 1/2`, `0 < α ≤ measAlpha0 m hm`). Admissible families are the
  structure `AdmissibleFamily m hm Π α` whose field `pair ν : IsFreqPair ...` is (H1)–(H2) verbatim (sup and Lipschitz
  bounds, `ε_ω, ε₁, ε₂ ∈ [0, α]`, `θ ∈ [0, θ₀]`), plus `K_ge : 2^ν ≤ K ν`; `Kprev` is `K_{ν-1}`, `K_{-1} = 0`. Maps are
  total functions constrained only on `D ν` (equivalent to maps on `D ν`).
* Normal modes are indexed by `ν : ℕ`, the Dirichlet mode `ν + 3` (landed `KAM.Wave.Normal` convention: `omegaNor`, `lamN`,
  `l : ℕ →₀ ℤ`), `normLab ν = ν + 3`; the decays `j⁻¹`, `j^{-1/2}` of (H2) are `(normLab ν)⁻¹`, `normLab ν ^ (-(1/2))`.
* `omegaTan m hm ξ = ω⁰(ξ)` and `omegaNor m hm ξ ν = Ω⁰_{ν+3}(ξ)` are the landed W0 definitions (`λ_J + Aξ`, `λ_ν + (Bξ)_ν`).
* Final glue for W8 (clause (1)): from `shell_defect_le` for each `k` and `α_k^{32/47}/t_k → 0` get
  `ε_k → 0` (a squeeze in `ℝ≥0∞` with `ENNReal.ofReal`); then `density_one_of_shells`. For clause (2): W6's `final-freq`
  gives `|⟨k, ω_*⟩| ≥ α̌/(2 A_k)`, so `isDiophantine_of_lower_bound` with `c = α̌/2` (τ = 24 > 1); and
  `tendsto_frequency_limit` with `e_k` the shell sup of `‖ω_* - ω⁰‖`.

## Build and lint
* Build (in import order, one module per call): `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpl
  KAM.Wave.Measure.{Coords,Lambda,UnpertBounds,Slab,Consts,Family,Pair,ZoneBound,SepLarge,Xzones,Dioph,Shells,Density,Limit,ZetaSum,Count,ZoneSums,MinusZones,RealBounds,MinusSum,PrepMinus,Prep,IterMinus,Iter,Measure,ShellEst}`:
  every module built with no error and no warning (last line `Built KAM.Wave.Measure.ShellEst`).
* `w_lint.sh /root/code/KAM-inp-wpl`: exit 0; tail: `check_lean_modules: PASS (3609 Lean files, ...)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (177 frozen declarations of KAM ...)`. `KAM/Root/Wave.lean` is the regenerated part (by
  `scripts/gen_root_imports.py`); no root was hand-edited.
* `#print axioms` of `exclSet_measure_le`, `exclSet_measurableSet`, `prepSet_measure_le`, `iterSet_measure_le`,
  `density_one_of_shells`, `shell_defect_le`, `isDiophantine_of_lower_bound`, `tendsto_frequency_limit`,
  `melnikov_prep_zero`, `measXSet_finite`, `tsum_lattice_le`, `IsFreqPair.zone_measure_le`, `volume_shell_diff_inner_le`:
  all `[propext, Classical.choice, Quot.sound]`.

## Deviations (none strengthens a hypothesis)
* `hatW` is defined by cases on `IsLamMinus` with `ŵ = ⟨l⟩ (j)^{-1/4}`, `j = sInf {ν | l ν ≠ 0} + 3` (the smaller label).
* `Xzone_measure_le` does not need `a ≤ α̂` (it is used only in the empty case, `Xzone_empty`); `largek` needs only `0 ≤ a ≤ β_*`.
* `shell_defect_le` assumes `MeasSetup m hm Π_k α_k` instead of the separate hypotheses `t₀ ≤ 1/2`, `α_k ≤ α₀`, `Π_k ⊆ {|ξ|_∞ ≤ 1/2}`.
  It also assumes `Π_k ⊆ (0, t_k)²` and `U_{-α_k} R_k ⊆ Π_k` as in the blueprint.
* `density_one_of_shells` takes `Γ ⊆ {I | ∀ i, 0 < I i}` and Borel `Γ`, and the shell defects `ε_k → 0` in `ℝ≥0∞`.
* The constants `σ_X`, `c_X` are `sInf` of the finite sets of the blueprint with default `1`, so they are the minima.

## Blueprint defects
None found that block the Lean statements. Remarks: in `bpW:w7:Xzones` the hypothesis `a ≤ α̂` is superfluous in the sloped case;
`bpW:w7:count` (i) is stated for all `N ≥ 1` but only used for `N ≥ 18`; in `bpW:w7:prep` the choice "`j₀ ≥ 3` since `α̂ ≤ 1/27`"
reads off `27^{4/11} ≥ 3` (checked as `three_le_rpow_neg`).

## Design signals
None: no module needed more than the default heartbeats; the largest (`UnpertBounds`, 413 lines) builds in seconds under the 4 GB cap.
