# W7-MEASURE handoff

Package W7-MEASURE (blueprint `blueprint-W/parts/w7-measure.tex`, `bpW:w7`), branch `inp-wpl`.
Off the frontier: source-faithful infrastructure used by several nodes; the dependency graph is still being built.
All modules are under `KAM/Wave/Measure/`, namespace `KAM.Wave`. No `sorry`, `axiom`, `maxHeartbeats` (or any budget
override); the largest file is 413 lines.

**Correction (audit 1, `W7-MEASURE-audit-1.md`).** The original claim "every blueprint label of the package is done" was
too strong: (F1) `shellInner` used a pointwise margin `∀ J ∉ R_k, a < dist I J` instead of the blueprint's
`dist_∞(I, ℝ² ∖ R_k) > a`, so `shell-est` had a stronger premise; (F2) parts of `freqcoords` (the `A⁻¹` formula,
`A⁻¹ b = (8π/21) λ_J`, `‖A‖_∞ = N_A`, `‖A⁻¹‖_∞ = L_A`, the affine bijection with its inverse) and of `count` (iii) /
`ext-zeta` (`Z₃ = ∑_{k≠0} |k|^{-3}` exactly, `Z₃ < 7`, `#{|k| = N} = 4N`) were not exported. Both are repaired in
section **W7-FIX** below; after W7-FIX every conclusion of every package label is exported.

## Files and the declarations proved, per blueprint label
| label | module | declarations |
|---|---|---|
| `freqcoords` | `Coords`, `CoordsInverse` | (W7-FIX) `actionAMat_inv`, `actionAMat_inv_mulVec_measBvec`, `abs_det_actionAMat`, `actionAMat_linfty_opNorm`, `actionAMat_inv_linfty_opNorm`, `omegaTanInv`, `omegaTan_bijective`, `omegaTanEquiv`; `measDA`, `measNA`, `measLA`, `measLA_eq`, `measNA_lt`, `measure_omegaTan_image`, `norm_omegaTan_sub_le`, `norm_sub_le_measLA_mul`, `omegaNor_eq`, `measS_eq`, `abs_measS_sub_le` |
| `indexdef` | `Lambda` | `normLab`, `japL`, `absWt`, `IsLam`, `IsLamMinus`, `hatW`, `kAbs`, `kAk`, `lam_cases` |
| `unpert-bounds` | `UnpertBounds` | `abs_measS_le`, `norm_omegaTan_le` (i); `three_betaStar_japL_le` (ii); `omegaNor_sub_approx` (iii); `abs_linF_omegaNor_sub_le` (iv) |
| `constdef`, `Xdef`, Xzones#consts | `Consts` | `measW`, `measTheta`, `measCLam`, `measKstar`, `measJstar`, `measXSet`, `measXSet_finite`, `measNX`, `measSigmaX(_pos/_le)`, `measCX(_pos/_le)`, `measTheta0`, `measAlpha0`, `measZ3`, `measCP`, `measCI`, `measC7`, `alphaHat`, `alphaCheck` |
| `zones`, `family` | `Family` | `MeasSetup`, `IsFreqPair` ((H1),(H2)), `AdmissibleFamily`, `zoneSet`, `prepZone`, `InZ`, `prepSet` (Ξ), `iterSet`, `exclSet` (ℰ), `isFreqPair_unpert` |
| `slab`, `ext-borel` | `Slab` | `measSlab_measure_le`, `volume_le_of_coord_slices`, `measurableSet_abs_lt_of_continuousOn` |
| `zone` | `Pair`, `ZoneBound` | `IsFreqPair.zone_measure_le`, `measure_abs_lt_le_of_growth`, `IsFreqPair.linF_lip`, `IsFreqPair.drift_le` |
| `sep`, `largek`, `dichotomy` | `SepLarge` | `IsFreqPair.normal_sep`, `zoneSet_zero_empty`, `IsFreqPair.largek`, `IsFreqPair.zone_dichotomy` |
| `Xzones` | `Xzones` | `IsFreqPair.Xzone_empty`, `IsFreqPair.Xzone_measure_le` |
| `count` | `Count`, `ZetaSum` | (i) `lamPlusFin`, `card_lamPlusFin_le`, `mem_lamPlusFin`; (ii) `tsum_Kprev_le`; (iii) (W7-FIX, module `ZetaExact`) `tsum_lattice_inv_cube`, `hasSum_lattice_inv_cube`, `measZ3_lt_seven`, `encard_l1Sphere_eq` (`ext-zeta`); the weighted upper bound `tsum_lattice_le` (with `encard_l1Sphere_le`) is what the measure estimate consumes |
| `prep` | `ZoneSums`, `MinusZones`, `MinusSum`, `PrepMinus`, `Prep` | `IsFreqPair.plus_bound`, `IsFreqPair.X_bound`, `IsFreqPair.minus_n_bound`, `minus_assembly`, `prep_minus_n_bound`, `prepSet_measure_le` |
| `iter` | `IterMinus`, `Iter` | `iter_minus_n_bound`, `iterSet_measure_le` |
| `measurable` | `Measure` | `exclSet_measurableSet` (Ξ, ℰ_it, ℰ, Π∖ℰ) |
| `measure` | `Measure` | `exclSet_measure_le`: `MeasurableSet ℰ ∧ volume ℰ ≤ ofReal (measC7 m hm * Metric.diam Π * α^(32/47))` |
| `melnikov` | `Measure` | `melnikov_prep`, `melnikov_prep_zero`, `melnikov_iter`, `melnikov_sep` |
| `shells`, `shell-geom` | `Shells` | `shellSet`, `shellInner` (W7-FIX: `Metric.infDist` to the complement), `mem_shellInner_iff`, `volume_shellSet`, `shellSet_disjoint`, `boxIoo_subset_iUnion_shell`, `shellSet_norm_ge`, `shellSet_dist_le`, `volume_shell_diff_inner_le` |
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

## W7-FIX (repair of `W7-MEASURE-audit-1.md`, findings F1–F2)

Branch `inp-w7land`. Both findings are repaired; no conclusion is weakened and no premise is added. New modules
`KAM/Wave/Measure/CoordsInverse.lean` (214 lines) and `KAM/Wave/Measure/ZetaExact.lean` (186 lines); `KAM/Root/Wave.lean`
regenerated by `scripts/gen_root_imports.py` (two added imports).

### AUDIT FOCUS

**F1 — inner shell (blueprint `bpW:w7:shells`, `w7-measure.tex:608-612`).**
* `KAM/Wave/Measure/Shells.lean:44` (changed definition):
  ```lean
  def shellInner (q t0 : ℝ) (k : ℕ) (a : ℝ) : Set (Fin 2 → ℝ) :=
    {I | I ∈ shellSet q t0 k ∧ a < Metric.infDist I (shellSet q t0 k)ᶜ}
  ```
  `Metric.infDist` for the sup-norm (Pi) metric of `Fin 2 → ℝ`, i.e. `dist_∞(I, ℝ² ∖ R_k) > a`.
* `Shells.lean:49` (new): `theorem mem_shellInner_iff : I ∈ shellInner q t0 k a ↔ I ∈ shellSet q t0 k ∧
  ∃ b, a < b ∧ ∀ J, J ∉ shellSet q t0 k → b ≤ dist I J` (the uniform-margin form named in the audit).
* `Shells.lean:168` (reproved, statement unchanged): `theorem volume_shell_diff_inner_le (hq : 0 < q) (hq1 : q < 1)
  (ht : 0 < t0) (k : ℕ) (ha : 0 < a) (hak : a ≤ shellT q t0 k) : volume (shellSet q t0 k \ shellInner q t0 k a) ≤
  ENNReal.ofReal (7 * a * shellT q t0 k)`. Proof: `C = ((0,t_k)²)ᶜ ∪ [0,t_{k+1}]²` is closed and contains `R_kᶜ`, so
  `IsClosed.exists_infDist_eq_dist` gives `J ∈ C` with `dist I J = infDist I C ≤ infDist I R_kᶜ ≤ a`; the outer layer is
  `(0,t)² ∖ (a,t-a)²` (≤ `4at`) and the inner one is `(0,s+a]² ∖ (0,s)²` (half-open, ≤ `3at` via `Real.volume_pi_Ioc`).
* `KAM/Wave/Measure/ShellEst.lean:30` (statement text unchanged, now over the corrected set): `shell_defect_le … (hinner :
  shellInner q t0 k αk ⊆ Pk) …`; the premise is now exactly `U_{-α_k} R_k ⊆ Π_k`. No other consumer of `shellInner`
  exists (grep over `KAM/`).
* Check: the audit's counterexample `I = (5/16, 5/16)`, `q = t0 = 1/2`, `k = 0`, `a = 1/16` was elaborated in a scratch
  probe as `I ∉ shellInner (1/2) (1/2) 0 (1/16)` (exit 0; probe removed).

**F2.1 — `bpW:w7:freqcoords` (blueprint lines 135-148), module `KAM/Wave/Measure/CoordsInverse.lean`.**
* `:33` `def measBvec : Fin 2 → ℝ := fun i => (lamTan m hm i)⁻¹` (`b`).
* `:37` `def measAinvMat := !![8π/21 * (-3 λ₁²), 8π/21 * (4 λ₁ λ₂); 8π/21 * (4 λ₁ λ₂), 8π/21 * (-3 λ₂²)]` (`λ_i = lamTan m hm (i-1)`).
* `:41` `actionAMat_mul_measAinvMat : actionAMat m hm * measAinvMat m hm = 1`; `:50` `measAinvMat_mul_actionAMat : measAinvMat m hm * actionAMat m hm = 1`.
* `:60` (i) `actionAMat_inv : (actionAMat m hm)⁻¹ = measAinvMat m hm`.
* `:64` (i) `abs_det_actionAMat : |(actionAMat m hm).det| = measDA m hm`.
* `:68` (i) `actionAMat_inv_mulVec_measBvec : ((actionAMat m hm)⁻¹).mulVec (measBvec m hm) = (8 * π / 21) • fun i => lamTan m hm i`.
* `:84` (ii) `actionAMat_linfty_opNorm : ‖actionAMat m hm‖ = measNA m hm` and `:130` (ii) `actionAMat_inv_linfty_opNorm :
  ‖(actionAMat m hm)⁻¹‖ = measLA m hm`, both under `open scoped Matrix.Norms.Operator` (section-local), i.e. Mathlib's
  `‖·‖_∞` = maximal absolute row sum (`Matrix.linfty_opNorm_def`), which is the operator norm on `(Fin 2 → ℝ, sup)`
  (`Matrix.linfty_opNorm_eq_opNorm`). `N_A < 3/5` and `L_A = N_A / D_A` were already `measNA_lt`, `measLA_eq` (`Coords`).
* `:176` (iii) `def omegaTanInv (ζ) := ((actionAMat m hm)⁻¹).mulVec (ζ - fun i => lamTan m hm i)`;
  `:183` `omegaTan_omegaTanInv : omegaTan m hm (omegaTanInv m hm ζ) = ζ`; `:189` `omegaTanInv_omegaTan :
  omegaTanInv m hm (omegaTan m hm ξ) = ξ`; `:194` `omegaTan_bijective : Function.Bijective (omegaTan m hm)`;
  `:200` `def omegaTanEquiv : (Fin 2 → ℝ) ≃ (Fin 2 → ℝ)` (toFun `omegaTan`, invFun `omegaTanInv`);
  `:208` affine form `omegaTan_eq_add_mulVec : omegaTan m hm ξ = (fun i => lamTan m hm i) + (actionAMat m hm).mulVec ξ`;
  helper `:179` `measAlin_eq_mulVec`.
* Documentation (`KAM/Wave/Measure/Coords.lean`): `measS` (`:47`) is now documented as the signed scalar
  `s(ζ) = ⟨λ_J, ζ - λ_J⟩` (not a norm); `omegaTan_sub` (`:131`) is documented as the difference identity
  `ω⁰ ξ - ω⁰ ξ' = A (ξ - ξ')` (injectivity is `ZoneBound.omegaTan_injective`); the module docstring no longer claims the
  norm identities live there. No statement in `Coords` changed.

**F2.2 — `bpW:w7:count` (iii) (line 451) and `bpW:w7:ext-zeta`, module `KAM/Wave/Measure/ZetaExact.lean`.**
* `:28` `encard_l1Sphere_eq {N : ℕ} (hN : 1 ≤ N) : (waveL1Sphere N).encard = 4 * N` (four disjoint injective
  quadrant families give `≥`; `≤` is the existing `encard_l1Sphere_le`).
* `:105` `tsum_lattice_inv_cube_ennreal : ∑' k : Fin 2 → ℤ, ENNReal.ofReal (if k = 0 then 0 else (kAbs k ^ 3)⁻¹) =
  ENNReal.ofReal measZ3` (fibre decomposition by `|k|₁` via `Equiv.sigmaFiberEquiv`, the exact count, `hasSum_zeta_two`).
* `:155` `hasSum_lattice_inv_cube : HasSum (fun k : Fin 2 → ℤ => if k = 0 then 0 else (kAbs k ^ 3)⁻¹) measZ3`
  (`measZ3 = 2π²/3`, `kAbs k = |k₁| + |k₂|`).
* `:174` `measZ3_lt_seven : measZ3 < 7`.
* `:181` `tsum_lattice_inv_cube : ∑' k : Fin 2 → ℤ, (if k = 0 then 0 else (kAbs k ^ 3)⁻¹) = measZ3 ∧ measZ3 < 7`
  (the literal statement `∑_{k≠0} |k|^{-3} = Z₃ < 7`).

Nothing was found infeasible; nothing is recorded as unformalized.

### W7-FIX checks
* Builds (one module per call): `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpl KAM.Wave.Measure.Shells
  KAM.Wave.Measure.ShellEst` and `… KAM.Wave.Measure.CoordsInverse KAM.Wave.Measure.ZetaExact KAM.Wave.Measure.ShellEst
  KAM.Wave.Measure.Dioph KAM.Wave.Measure.Limit` (the three leaves cover every Measure module): each
  `Build completed successfully`; single-file checks of the three edited/new files printed no warning.
* `#print axioms` of `mem_shellInner_iff`, `volume_shell_diff_inner_le`, `shell_defect_le`, `actionAMat_mul_measAinvMat`,
  `measAinvMat_mul_actionAMat`, `actionAMat_inv`, `abs_det_actionAMat`, `actionAMat_inv_mulVec_measBvec`,
  `actionAMat_linfty_opNorm`, `actionAMat_inv_linfty_opNorm`, `measAlin_eq_mulVec`, `omegaTan_omegaTanInv`,
  `omegaTanInv_omegaTan`, `omegaTan_bijective`, `omegaTan_eq_add_mulVec`, `encard_l1Sphere_eq`,
  `tsum_lattice_inv_cube_ennreal`, `hasSum_lattice_inv_cube`, `measZ3_lt_seven`, `tsum_lattice_inv_cube`: each
  `[propext, Classical.choice, Quot.sound]`.
* Lint: `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpl` exit **0**; tail:
  `check_lean_modules: PASS (3689 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, …)`. (A first run exited 1 on a
  108-character docstring line in `Shells.lean`; it was rewrapped, rebuilt and lint rerun.)
* Short names: `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wpl
  <all 28 KAM.Wave.Measure modules>` → `short-name check OK (no reused public short name)`, exit 0.
* Note: commit `ae55fbef` (F2.1) includes the regenerated root part, which already imports `ZetaExact`; that module
  lands in the next commit `406109f0` (F2.2). Build the branch tip, not the intermediate commit.
