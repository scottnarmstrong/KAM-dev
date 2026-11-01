# LP-SP-PROD handoff (track LP, non-frozen; MAIN Lemma 17 for n bodies, L18 line 595, (45) summed, (47))

## Files (all new; namespace `KAM.Planetary.Spatial`; largest 244 lines; no heartbeat/recursion option)
`KAM/Planetary/Spatial/Product.lean` (facade) and `Product/{Defs,Chart,Deficit,Split}.lean`.
Only existing file touched: generated `KAM/Root/Planetary.lean` (`scripts/gen_root_imports.py`, needed for lint).
Prerequisite modules `Spatial.{Vector,Model,Elements}` were rebuilt (capped) first; unchanged.

## Layout (read first)
`w : Phase (n + (n + n))`: `w.1 = (λ | ξ | v)`, `w.2 = (I | η | u)` (`fast w.1 = λ`, `slow w.1 = (ξ | v)`,
`fast w.2 = I`, `slow w.2 = (η | u)`); `n` fast and `2n` slow pairs, so `slow w` is the slow pair of
`Nekhoroshev.PartialBlock n (n + n)`. Body block `spatialBlock w i = (![λ_i, ξ_i, v_i], ![I_i, η_i, u_i]) : Phase 3`
(LP-SP-CHART slot convention). Output `Phase (n * 3)` (body-major, `bodyVector3`), as `Spatial.Model`.

## Declarations
Defs: `spatialBlock`, `ofSpatialBodies`, `unblockSpatial`, `spatialPoincareProd ν w = ofSpatialBodies fun i =>
spatialPoincare (ν i) (spatialBlock w i)`, `spatialPoincareProdDom n = {w | ∀ i, spatialBlock w i ∈ spatialPoincareDom}`,
`spatialRegionProd ν`, `spatialActions`, `spatialGammaBody`, `spatialZBody`, `spatialProdShift k w = w + fastShift k`,
`spatialBlockCLM`, `ofSpatialBodiesCLM`; `isOpen_spatialPoincareProdDom`, `symplecticForm_spatialBlocks`,
`symplecticForm_ofSpatialBodies`, `spatialBlock_shift`.
Chart (item 2), all `(hν : ∀ i, 0 < ν i)`:
- `analyticOnNhd_spatialPoincareProd : AnalyticOnNhd ℝ (spatialPoincareProd ν) (spatialPoincareProdDom n)`
- `spatialPoincareProd_lattice : w ∈ dom → spatialProdShift k w ∈ dom ∧ spatialPoincareProd ν (spatialProdShift k w) = spatialPoincareProd ν w`
- `spatialPoincareProd_symplectic : IsSymplecticOn 1 (spatialPoincareProd ν) (spatialPoincareProdDom n)`
- `spatialPoincareProd_image : spatialPoincareProd ν '' spatialPoincareProdDom n = spatialRegionProd ν`
- `spatialPoincareProd_eq_iff : Ψ w = Ψ w' ↔ ∃ k : Fin n → ℤ, w' = spatialProdShift k w` (w, w' in dom)
- `spatialPoincareProd_fderiv_equiv`, `spatialPoincareProd_localDiffeo` (OpenPartialHomeomorph, analytic inverse).
Deficit (item 3), on dom:
- `spatialKeplerAction_spatialPoincareProd : spatialKeplerAction ν (Ψ w) i = spatialActions w i`
- `angularMomentum3_dot_e₃_spatialPoincareProd : angularMomentum3 (Ψ w) ⬝ᵥ e₃ = ∑ i, (I_i - Γ_i - Z_i)`
- `spatialFixedPlaneDeficit ν z := ∑ i, spatialKeplerAction ν z i - angularMomentum3 z ⬝ᵥ e₃`;
  `spatialFixedPlaneDeficit_spatialPoincareProd : = ∑ i, (Γ_i + Z_i)`;
  `spatialFixedPlaneDeficit_eq_half_slow_sq : = ((∑ k, slow w.1 k ^ 2) + ∑ k, slow w.2 k ^ 2) / 2`
- `spatialStrongAMD_spatialPoincareProd_of_aligned (hL : L = spaceLength L • e₃) : spatialStrongAMD ν (Ψ w) = ∑ i, (Γ_i + Z_i)`
  (the alignment `hL` is the L18 typing premise); bonus `spatialStrongAMD_le_spatialFixedPlaneDeficit` (all z).
Split (item 4): `fSpatial ν z := spaceSq (∑ p_i)/2 - ∑_{i<j} ν_iν_j/|q_i - q_j|`, `spatialHProd ν w := -∑ ν_i^3/(2 I_i^2)`;
`spatialHamiltonian_split` (identically `H = ∑ ν_iE_i + μ fSpatial`, `rfl`), `spatialHamiltonian_spatialPoincareProd :
H_μ (Ψ w) = spatialHProd ν w + μ * fSpatial ν (Ψ w)` on dom, `analyticOnNhd_fSpatial`,
`analyticOnNhd_fSpatial_spatialPoincareProd` (on dom ∩ Ψ⁻¹(collision-free)), `isOpen_spatialPoincareProd_preimage`,
`analyticOnNhd_spatialHamiltonian_spatialPoincareProd`.

## Not done
Nothing omitted. The planar `phaseCast` equal-dimension variant (`poincareProdCast`) was not replicated (not in brief).

## Checks
- `lp_build.sh` (one module per call, import order): `Product.{Defs,Chart,Deficit,Split}` then `Product`: all `Build completed successfully`; no `sorry` warning.
- `lp_lint.sh`: exit 0 (`check_lean_modules: PASS (3730 Lean files...)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`) (first run flagged one 101-char line; fixed).
- `main_shortname_check.py`: `short-name check OK`, exit 0.
- `#print axioms` (`.drafts/ax_spprod.lean`, via `lp_lean.sh`): all 14 main declarations (names in the file) depend on exactly `[propext, Classical.choice, Quot.sound]`.
- Every module docstring contains the SPEC §4 sentence.

## AUDIT FOCUS
- Slot order in `spatialBlock` / `blockSlots` (`castAdd (n+n)`, `natAdd n (castAdd n)`, `natAdd n (natAdd n)`) and `unblockSpatial`; `symplecticForm_spatialBlocks` (sum over the three slots; form is `Σ dI∧dλ + dη∧dξ + du∧dv` per body).
- `spatialPoincareProd_eq_iff`: lattice is only `λ_i ↦ λ_i + 2π k_i`, `fastShift (a:=n) (b:=n+n)`.
- Bridge `spatialKeplerEnergy_eq_spatialEnergy` (model `spaceSq/spaceLength` vs chart `⬝ᵥ/√`) and `planetAngularMomentum3_eq_cross`.
- `spatialFixedPlaneDeficit` uses `⬝ᵥ e₃` (third component); aligned theorem takes `L = |L| • e₃` as hypothesis (typing/alignment, not a conclusion).
- `fSpatial` recoil term is `|Σ p|²/2`, literally MAIN (1) as in `spatialHamiltonian`.

## Errata / deviations / design signals
No MAIN defect found. Deviation: `Phase (n + (n + n))` rather than `n + 2*n` (`2*n` is not defeq to `n+n`). Design signals: none (files build in 5–15 s).
