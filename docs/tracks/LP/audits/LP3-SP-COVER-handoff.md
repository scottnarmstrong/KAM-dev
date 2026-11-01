# LP3-SP-COVER handoff (spatial finite cover and normalized perturbation, `k = n + n`)

Branch `inp-lp-lp3spcov`. Track LP, non-frozen. No `sorry`, no heartbeat overrides, no existing file edited
(except the generated `KAM/Root/Planetary.lean`: two import lines from `scripts/gen_root_imports.py`).

## Files
- `KAM/Planetary/Spatial/Nek/Cover.lean` (163 lines): cells, containment, slow gap.
- `KAM/Planetary/Spatial/Nek/Perturbation.lean` (271 lines): perturbation, region `V_j`, identity, bundle.
Imports: planar `StrongAMD.Nek.Cover` (reused verbatim; it pulls track P `Exponential.Stopped`, which
public-imports the SEALED anchor, D58; no provider), spatial `AnalyticDomain.{Containment,Extension}`,
`ChartLift.Setting`, `Exponential.{Hamiltonian,Lift}`.

## Reused, not duplicated (planar, generic in the action space `Fin n → ℝ`)
`nekWidth/Eta/Rho` (+ lemmas), `nekCellInner/Outer`, `nekCellLevel`, `nekCell_level_le`, `nekCell_collar`,
`IsNekCover`, `exists_isNekCover`, `nekCell_mem_innerCore`, `IsNekCover.mem_innerCore`,
`nekCell_threshold_bound(_of_close)`, `norm_sub_ofReal_re_eq`. No planar lemma needed generalizing.

## Declarations (namespace `KAM.Planetary.Spatial`)
Cover.lean:
- `spatialNekCellSlow ν δ c = slowBall (n + n) (nekCellLevel ν δ c)` (`D_j ⊆ Phase (n + n)`), `isOpen_spatialNekCellSlow`.
- `spatialNekCell_containment : c ∈ 𝓛_δ → partialComplexDomain (nekCellOuter rg R c) (spatialNekCellSlow ν δ c) (nekRho rg R) ⊆ complexTubeNM (spatialStrongCore ν L δ rg) (R / 2)`
  (tube of `exists_spatialStrongTube`; via `spatialStrongCore_containment`, `s = b = η`, `rs = nekWidth`).
- `spatialNekCell_slowGap_pos`, `exists_spatialNekSlowGap`: `∃ εD > 0, ∀ c ∈ s, ∀ 0 ≤ ε < εD,
  √(2 (B c − 3δ/8)) + √(2 * ((n + n : ℕ) : ℝ)) * ε < √(2 (nekCellLevel ν δ c))` (hypothesis of
  `stopped_slow_erosion` at `n + n` slow pairs; the constant is `√(2·2n)`).

Perturbation.lean:
- `IsSpatialStrongExtension ν L δ rg R M fc` (four clauses of `exists_spatialStrongTube`), `exists_isSpatialStrongExtension`.
- `spatialNekNormalizedPerturbation ν L δ rg R fc B0 z = if z ∈ complexTubeNM core R then fc z / B0 else 0`.
- `isPartialPerturbation_spatialNekCell`, `isPartialPerturbation_neg_spatialNekCell` (hyps `0<rg, 0<R, 0<δ, 0<B0, M ≤ B0, c ∈ 𝓛_δ`).
- `spatialNekCellRegion` (`V_j`), `isOpen_spatialNekCellRegion`, `complexifyPhase_mem_spatialNekCell`, `spatialNekCell_region_trace`.
- `spatialNekCell_hamiltonian_eq`: on `V_j`, `degenerateHamiltonian (realPart (planetaryKeplerC ν)) (fun _ x => (P (complexifyPhase x)).re) (B0 * μ) w = spLiftChartHam ν μ w`.
  The chart Hamiltonian is `spLiftChartHam` (`spatialHProd ν + μ · fSpatial ν ∘ Ψ`), the one SP-LIFT's lift solves. No division/time rescaling (as planar).
- `spatialNekCell_field_eq`: `DifferentiableAt` and equality of `hamiltonianVectorField` on `V_j`.
- `exists_spatialNekPerturbation`: `∃ R > 0, ∃ B0 ≥ 1, ∃ P, (∀ c ∈ 𝓛_δ, IsPartialPerturbation ± P on (G′_c, D_c, ρ)) ∧ ∀ c ∈ 𝓛_δ, ∀ μ, ∀ w ∈ V_c, w ∈ spatialChartSafe ν ∧ identity ∧ DifferentiableAt ∧ field equality`
  (same quantifier order as `exists_nekPerturbation`; hypotheses `hν, 2 ≤ n, IsCompact L, L ⊆ chamber ν, IsSharedTube ν L δ rg, 0 < δ`).

## Not done / notes
- Cell statements hold for every centre in 𝓛_δ, not only the finite cover (as planar).
- Domain note: `w ∈ spatialChartSafe ν` and `w ∈ spLiftChartSafe ν` are definitionally the same set; the proof uses `exact` across them.
- No spatial sharpened stopped bound / threshold minimum (those belong to the drift packages).

## Checks
- `lp_build.sh /root/code/KAM-inp-lp-lp3spcov KAM.Planetary.Spatial.Nek.Cover`: `✔ Built` (9353 jobs), no warning in my file.
- `lp_build.sh ... KAM.Planetary.Spatial.Nek.Perturbation`: `✔ Built KAM.Planetary.Spatial.Nek.Perturbation`, Build completed successfully (9360 jobs).
- `main_shortname_check.py` on both files: exit 0, `short-name check OK (no reused public short name)`.
- `lp_lint.sh`: after `gen_root_imports.py`: `check_lean_modules: PASS (3781 Lean files)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`
- `#print axioms` (`.drafts/ax_spcover.lean` via `lp_lean.sh`): `spatialNekCell_containment, exists_spatialNekSlowGap,
  isPartialPerturbation_spatialNekCell, isPartialPerturbation_neg_spatialNekCell, spatialNekCell_hamiltonian_eq,
  spatialNekCell_field_eq, exists_spatialNekPerturbation`: all `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
1. Containment widths: `4η = rs ≤ R/4 < R/2`; `hact` bound `2η + ρ < 4η = rs`; angle bound `ρ < 4η`.
2. The sum split `∑_{k<n+n}(y₁²+y₂²)/2 = (∑y₁² + ∑y₂²)/2` linking `slowBall (n+n)` to `spatialSecularBall`.
3. `nekCellLevel ≤ B(c) − δ/4` (δ>0) so `D_j ⊆ spatialSecularBall`.
4. Slow gap: `B(c) ≥ δ` gives `A′_j = B(c) − 3δ/8 ≥ 5δ/8 > 0`; constant `√(2 (n+n))`.
5. `spatialNekCell_hamiltonian_eq`: sign/scale (`B0 * μ`), `spatialHProd = keplerSumGen ℝ ν (fast w.2)`.
6. `exists_spatialNekPerturbation` quantifier order: `R, B0, P` depend only on `(ν, L, δ, rg)`.

## Errata / deviations / design signals
No source defects found. No deviations beyond the all-centres bundling. No heartbeat issues (each file builds in under 10 s;
163 and 271 lines).
