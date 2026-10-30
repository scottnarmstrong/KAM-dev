# Handoff SO-R1B: R1 package with M = 203/100

## Files
- changed `KAM/SpinOrbit/LunarParams.lean` (136 lines). No other files.

## Diff (summary)
- `lunarR1.M`: `1987 / 1000` → `203 / 100`, with the signatures' one-line comment
  (`-- \`M\` must exceed the D²H sum of \`checkHamBounds\`, 2.0205 on both R1 tori.`); body now
  matches `SOSignaturesLunar.lean` §I.4 lines 361-378 exactly. σK, σB, σT unchanged (1987/1000).
- Module docstring: `M = 203/100` (ruling D29) stated separately from σK = σB = σT.
- `lunarR1_smallness_C1`: restated at err = 9·10⁻⁷⁶ (was 10⁻⁷⁵).
- `lunarR1_smallness_C1_fails`: restated at err = 10⁻⁷⁵ (was 10⁻⁷⁴).
- `lunarR1_smallness_C2`: restated at err = 9·10⁻⁷⁶, disp = 10⁻³⁹ (was err = 10⁻⁷⁵).
- Unchanged and re-checked: `lunarR1Kappa_div`, `lunarR1_staticCore(_zero)`, `lunarR1_err_nonneg`,
  `lunarR1_staticCore_gen2`, `lunarR1_rayMargins`, `lunarR1Box_normLo` (none reads M except the
  static core `0 < M`). All names kept.

## New threshold and margins (exact ℚ, computed by `#eval` of the very expressions in the theorems)
- T := γ⁴ρ⁴ / isoC1Q(2, τ, ρ, ρ∞, M, σK, σB, σT, μ, ν, γ̄) =
  5415673711196611889500450363905948435681950325656135570526123046875 /
  5541893568355888510943158276183704823811240097690100147758596141563896907077199650084272944402787269610404669483257062655014116150061547126784
  = 9.7722441696e-76, log10 T = −75.0100057 (was −74.669083 at M = 1.987; M raise costs 10^{0.341}).
- Kernel brackets: 9·10⁻⁷⁶ < T < 10⁻⁷⁵ (`lunarR1_smallness_C1` true, `_C1_fails` false).
- Margins of the SO-GEN2 budgets (T / budget, exact rationals then decimal):
  - 4.03e-78: ×242.487 (10^{2.385})
  - 7.84e-78: ×124.646 (10^{2.096})
  Cross-check: 9.772e-76 / 4.03e-78 = 242.5 ✓; / 7.84e-78 = 124.6 ✓. (Ratios printed with Python
  `fractions`/40-digit `Decimal` from the Lean rationals.)
- C₂ factor k := isoC2Q / (γ²ρ²) = 45925799347544020570983273203846743840910961055557416637225569878016 /
  268717291620682321124048534765625 = 1.70907e35, log10 = 35.232761 (was 35.065965).
  Required disp ≥ k·err: at 9e-76 → 1.538e-40 (10⁻³⁹ passes); at the SO-GEN2 budgets
  4.03e-78 → 6.89e-43, 7.84e-78 → 1.340e-42.
- Ray margins unchanged (do not involve M): L = κ ≈ 1.896, slack ≈ 1.896 on (s−1).

## Checks
- `inp_lake_build.sh <wt> KAM.SpinOrbit.LunarParams`: `✔ Built KAM.SpinOrbit.LunarParams (5.9s)`, no errors.
  (A first build with the old C₁ statements failed as expected: C₁ at 10⁻⁷⁵ is now false.)
- `scripts/lint_sources.sh`: check_lean_modules PASS (1382 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK
  (only note: "KAM.lean is out of date" — generated file, not mine to regenerate).
- `main_shortname_check.py <wt> KAM.SpinOrbit.LunarParams`: OK. No lines > 100 columns in the file.
- No heartbeat overrides, no native_decide.

## Axioms
lunarR1_smallness_C1, _C1_fails, _C2, _staticCore_gen2, _rayMargins, lunarR1Kappa_div,
lunarR1Box_normLo, lunarR1_staticCore: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
- None suspected in sources. The docstring phrase "one majorant" now precedes only σK = σB = σT.
- Threshold headroom over 10⁻⁷⁵ is gone: SO-DATA budgets must stay below 9.77e-76.

AUDIT FOCUS (delta audit against the audited SO-R1, c2a05fa3): (1) the ONLY change to declarations is lunarR1's field M := 203/100 (σK, σB, σT stay 1987/1000), matching the updated signed body in /root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean §I.4 (lines 361-378); the rest of the diff is restated helper pre-checks and docstrings; (2) the reason: SO-DATA-1's mirror D²H sum 2.02053 for soRotHamExprScaled (237/125) on D; spot-check that value independently from the landed hamBoundsOk form if feasible (it is the binding conjunct), and that 203/100 exceeds it; (3) the pre-checks are non-vacuous and bracket the new threshold (9·10⁻⁷⁶ passes, 10⁻⁷⁵ fails), with the C₂ factor; verify the handoff's margins of the SO-GEN2 budgets (×242.5, ×124.6) exactly; (4) kernel replay, axioms, lint, 100 columns.
