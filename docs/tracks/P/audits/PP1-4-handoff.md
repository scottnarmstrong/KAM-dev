# PP1-4 prover handoff (branch inp-pp14, 1178f45; contains inp-pp11 (PP1-1, delivered); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- New: `KAM/Planetary/Hamiltonian/Chart.lean` (247 lines). Nothing else changed. `KAM.lean` not edited.

## Nodes proved (all declarations of the signature section B, copied verbatim, no signature changed)
- chart: `IsChart`, `isChart_iff`, `IsChart.analyticOnNhd/.symplectic/.mono`, `chartPullback`, `IsChart.bijective_fderiv`
- li-det: `IsChart.abs_det_fderiv`
- chart-field: `chart_field_differentiableAt_iff`, `chart_field`
- chart-orbit: `chart_orbit`
- typical (2)(3): `IsChart.comp`, `chartPullback_comp`, `isChart_continuousLinearEquiv`
- conv#data: `angleScale`, `angleScaleCLM`, `angleScaleCLM_apply`, `fullShift`, `fullShift_eq_angleScale`
- period-convert (a): `isChart_angleScale`, `angleScale_add_angleShift`, `abs_det_fderiv_angleScale`, `volume_angleScale_image`
- period-convert (b): `chartPullback_angleScale`, `angleScale_hamiltonianVectorField`
- period-convert (d): `fastShift_eq_angleScale`

## Approach
- `bijective_fderiv`/`abs_det_fderiv`: PP1-1 `bijective_of_symplectic`/`abs_det_of_symplectic` at `A = fderiv Ψ z`.
- `chart_field_differentiableAt_iff` (⇒): analytic gives `HasStrictFDerivAt`; `DΨ z` bijective gives a CLE
  (`LinearEquiv.ofBijective ... .toContinuousLinearEquiv`); `to_localInverse`; `H = c • H^Ψ ∘ localInverse` near `Ψ z`
  via `eventually_right_inverse`, `localInverse_apply_image`, `congr_of_eventuallyEq`.
- `chart_field`: `fderiv_comp` + `apply_linearField_comp_of_symplectic` (private `linearField_smul`); non-differentiable
  branch both sides `0` (private `linearField_zero`).
- `chart_orbit`: `HasFDerivAt.comp_hasDerivAt` + `chart_field`. `IsChart.comp`: `AnalyticOnNhd.comp` + `IsSymplecticOn.comp`, `mul_comm`.
- `angleScale`: `rfl`-equal to `angleScaleCLM` (private `angleScale_eq_clm`), `ContinuousLinearMap.fderiv`, symplectic by `simp; ring`.
- `volume_angleScale_image`: `Measure.addHaar_image_continuousLinearMap`.

## Design note N1 (audit): Haar helper
`isAddHaarMeasure_volume_phase` is NOT declared here (it stays owned by PP1-7/Liouville as in the signature file).
`volume_angleScale_image` installs the instance locally with `have : ... := Measure.prod.instIsAddHaarMeasure _ _`.
No Chart -> Liouville dependency, no duplicate declaration. (If the orchestrator prefers the audit's
"move helper to Chart", that is a one-line move; not done to avoid a conflict with the PP1-7 brief.)

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-pp14 KAM.Planetary.Hamiltonian.Chart`: "Build completed successfully (9055 jobs)";
  only linter warnings: unused `hc` in `isChart_angleScale` (signature-mandated binder) and in PP1-1's `abs_det_of_symplectic`.
- `sh scripts/lint_sources.sh`: no over-length lines; check_lean_modules PASS (417 files); FROZEN-ANCHOR GUARD OK;
  ABI HASHES OK (144). It prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated root, owner/orchestrator regenerates; I did not edit it).
- No `sorry`, `set_option`, axiom, etc. in the file (grep).
- `#print axioms` for chart_field, chart_orbit, chart_field_differentiableAt_iff, IsChart.comp, volume_angleScale_image,
  angleScale_hamiltonianVectorField, fastShift_eq_angleScale, IsChart.abs_det_fderiv, isChart_continuousLinearEquiv:
  all `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations / design signals
- None: no statement was false, no heartbeat problems, no suspected errata. Deviations: only the N1 choice above.

AUDIT FOCUS (design docs/tracks/P/design/PART1-LEAN-DESIGN.md row P1-4 (Chart) and proof plan; its audit DESIGN-P1-design-audit-1.md; KEPLER design Part 1 dependency (item 8); blueprint-P p1 chart, chart-field, chart-orbit, typical (2)(3), period-convert (a)(b)(d), li-det): (1) statements = design signatures and blueprint; IsChart = AnalyticOnNhd + IsSymplecticOn as designed, consumable by the delivered Kepler/Poincaré code; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the PP1-4 module(s) (KAM/Planetary/Hamiltonian/Chart*).
