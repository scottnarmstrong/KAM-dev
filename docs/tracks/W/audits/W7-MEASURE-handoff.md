# W7-MEASURE handoff (PARTIAL STATE; see the end for what remains)

Branch `inp-wpl`, modules under `KAM/Wave/Measure/` (namespace `KAM.Wave`). Off the frontier: source-faithful
infrastructure; the dependency graph is still being built.

## Done (compiles, no sorry), with blueprint labels
- `Coords`: `bpW:w7:freqcoords` (`measDA`, `measNA`, `measLA`, `measS_eq`, `omegaNor_eq`, `measure_omegaTan_image`,
  `norm_omegaTan_sub_le`, `norm_sub_le_measLA_mul`, `abs_measS_sub_le`).
- `Lambda`: `bpW:w7:indexdef` (`japL`, `absWt`, `IsLam`, `IsLamMinus`, `hatW`, `kAbs`, `kAk`, `lam_cases`).
- `UnpertBounds`: `bpW:w7:unpert-bounds` (`abs_measS_le`, `norm_omegaTan_le`, `three_betaStar_japL_le`,
  `omegaNor_sub_approx`, `abs_linF_omegaNor_sub_le`).
- `Consts`: `bpW:w7:constdef`, `bpW:w7:Xdef` (`measXSet`, `measXSet_finite`, `measSigmaX`, `measCX`, `measTheta0`,
  `measAlpha0`, `measC7`, `alphaHat`, `alphaCheck`).
- `Family`: `bpW:w7:zones`, `bpW:w7:family` (`IsFreqPair`, `AdmissibleFamily`, `zoneSet`, `prepZone`, `prepSet`,
  `iterSet`, `exclSet`).
- `Slab`: `bpW:w7:slab`, `bpW:w7:ext-borel`.
- `Pair`, `ZoneBound`: `bpW:w7:zone` (`IsFreqPair.zone_measure_le`).
- `SepLarge`: `bpW:w7:sep`, `bpW:w7:largek`, `bpW:w7:dichotomy`.
- `Xzones`: `bpW:w7:Xzones`.
- `Dioph`: `bpW:w7:dioph`. `Shells`: `bpW:w7:shells`, `bpW:w7:shell-geom`. `Density`: `bpW:w7:density`.
  `Limit`: `bpW:w7:limit`.

## Remaining at the time of this note
count, prep, iter, measure (the final theorem), melnikov, measurable, shell-est.
