# Handoff SO-R1: lunar parameter package R1

## Files
- new `KAM/SpinOrbit/LunarParams.lean` (134 lines, Lean module, imports `KAM.Certificate.Defs` only).

## Declarations
Signed (exactly as in `SOSignaturesLunar.lean` §I.4): `lunarR1TimeScale`, `lunarR1Scalar`,
`lunarR1Kappa`, `lunarR1`, `lunarR1Kappa_div` (proof: `decide +kernel`).
Placeholders `lunarLower/UpperErr/Disp` NOT written (SO-DATA's).

Helpers (distinct names): `lunarR1StaticCore` (Bool: parameter-only conjuncts of `checkStatic`
except `0 ≤ err`), `lunarR1_staticCore_zero`, `lunarR1_staticCore`, `lunarR1_err_nonneg`,
`lunarR1_staticCore_gen2`, `lunarR1_smallness_C1`, `lunarR1_smallness_C1_fails`,
`lunarR1_smallness_C2`, `lunarR1Box`, `lunarR1_rayMargins`, `lunarR1Box_normLo`.

## Pre-check results (all `decide +kernel`; whole file builds in 4.6 s; the largest single
declaration type-check is 0.25 s, the rest ≤ 0.14 s)
1. Static parameter part: holds for every `err`, `disp` (`lunarR1_staticCore`, by `rfl` reduction
   to `lunarR1 0 0`, since the core reads no `err`/`disp`), plus `0 ≤ err` from the hypothesis
   (`lunarR1_err_nonneg`). Also at the SO-GEN2 budgets with literals 4.1e-78 and 7.9e-78
   (`lunarR1_staticCore_gen2`). Shapes, weights, the π enclosure and the box are certificate data
   and are not in scope.
2. Smallness (C₁): PASSES at err = 10⁻⁷⁵ (`lunarR1_smallness_C1`) and FAILS at 10⁻⁷⁴
   (`lunarR1_smallness_C1_fails`). Computed by exact `ℚ` evaluation:
   log10(γ⁴ρ⁴ / isoC1Q) = −74.669083, matching the design's 10^{−74.669}. Margins at the SO-GEN2
   budgets: 4.03e-78 is 10^{-3.73} of threshold (×~5300), 7.84e-78 is ×~2700.
   C₂: log10(isoC2Q / (γ²ρ²)) = 35.065965, so `disp ≥ err · 1.164e35` is needed; at err = 10⁻⁷⁵,
   disp = 10⁻³⁹ passes (`lunarR1_smallness_C2`). At the SO-GEN2 budgets, disp ≈ 4.7e-43 / 9.2e-43
   minimum (SO-DATA should pick literals above these).
3. Ray margins: boxes `lunarR1Box a b` = [(κ((a + b·2.236068)/3118 − 1), κ|b|/3118·10⁻⁶), (κ, 0)]
   for ν₋ (a,b) = (3039, 1) and ν₊ (3197, −1) (√5 ∈ [2.236067, 2.236069] covered). Coordinate 1 is
   κ exactly, so `freqNormLo = κ ≈ 1.89600` (`lunarR1Box_normLo`), and both margins hold
   (`lunarR1_rayMargins`): need L ≥ ν/(s−1) = 1 and L ≥ ν/(σω − s) ≈ 1.000001e-6; slack factor
   ≈ 1.896 on the binding (s − 1) margin. Any box whose second entry is (κ, 0) gives L = κ.

## Checks
- `inp_lake_build.sh … KAM.SpinOrbit.LunarParams`: `✔ Built KAM.SpinOrbit.LunarParams (4.6s)`,
  no warnings in this file.
- `scripts/lint_sources.sh`: check_lean_modules PASS (1381 files), FROZEN-ANCHOR GUARD OK, ABI
  HASHES OK.
- `main_shortname_check.py`: OK (no reused public short name). No lines > 100 columns.
- No native_decide / heartbeat overrides.

## `#print axioms`
All eleven theorems (incl. `lunarR1Kappa_div`): [propext, Classical.choice, Quot.sound].

## Uncertainties / deviations / errata
- `KAM.lean` (generated) not regenerated; the orchestrator should run `gen_root_imports.py`.
- No suspected errata. `lunarR1_staticCore` covers the parameter conjuncts only; `n = 2` and the
  `2 ≤ n`, `n ≤ τ + 1` conjuncts are encoded as `2 ≤ p.tau + 1` in the core.
