# SHARP2-B3: `ModConstants` (defs, positivity, monotonicity)

Branch `sharp-b3` (from `sharp-v2`). Additive; nothing existing is edited.

## Files
- `KAM/Sharp2/ModConstants.lean` (132): `StepIn`, `StepConsts`, `stepConsts`, `stepCond`, **verbatim** from
  `APOST-SHARP-V2-SIGNATURES.lean.txt` (checked by string containment of the signature block).
- `KAM/Sharp2/ModConstantsData.lean` (180): `StepIn.Ok` (admissible data), `StepIn.Le` (the order in which the
  engine varies inputs), `Bd`, and one definition per `let` of `stepConsts` (`sg`, `sCE`, ..., `sQL`).
- `KAM/Sharp2/ModConstantsBd.lean` (646): `bd_X : Bd X p p'` (= `0 ≤ X p ≤ X p'`) for each helper, by
  `positivity`/`gcongr` (one declaration each, default heartbeats, no overrides).
- `KAM/Sharp2/ModConstantsMono.lean` (216): `stepConsts_eq` (`rfl`), `StepConsts.{Nonneg,LeCore,Le}`,
  `stepConsts_nonneg`, `stepConsts_mono`, `stepConsts_mono_iso`, `stepConsts_mono_sd`, `stepConsts_mono_delta`,
  `stepConsts_monoCore_delta`, `stepConsts_CxiL_pos`, `stepCond_anti`.
- `scripts/apost_sharp/check_modconst_v2.py`: mechanical translation of the Lean `stepConsts` text to Fractions and
  comparison with `stageB`.
- `KAM.lean` regenerated.

## What is proved
`StepIn.Le p p'`: same `n, κ, r, ϑ, ϑ_ξ, ϑ_Ω, q`, same step kind; `c, c¹, c̄, δ`, caps `M1 M2 σ_*`, `t`, `λ`, `γ̄`, `Θ, y0,
Mh2, λ_ω` all larger.
- `stepConsts_nonneg`: all 23 constants ≥ 0 (plain and iso).
- `stepConsts_mono` (plain step): `p ≼ p'` ⇒ every constant, including `QbN` and `Q`, is ≤.
- `stepConsts_mono_iso` (iso step): same for all constants **except `QbN` and `Q`**.
- `..._mono_sd` (raising `c, c¹, c̄, δ`), `..._mono_delta` (bite only), `stepConsts_CxiL_pos` (`C_ξL > 0` for `c, λ > 0`),
  `stepCond_anti` (conditions persist for smaller `X`).

## Design signal (not a Lean failure): iso `QbN` is not monotone in the small-divisor constants
`bpI:p2s2:constants` adds to `Q̄_N` the term `(1+nϑ_ξ) Θ C_Ω Q̃_N C_0 ϑ_ξ / C_ξL` with `C_ξL = c·C_gL`. The blueprint remark
("all constants are polynomials with nonnegative coefficients ... nondecreasing in each argument") is false for it:
`c` sits in a denominator. Exact-Fraction search (the script, iso, 2000 random admissible inputs): doubling `c` *decreases* `QbN`
in 1123/2000 cases (example in the script output: c = 0.13 → 0.26 gives QbN 53892 → 39799). Doubling `δ` at fixed `c`
never decreased it in the sample, but I cannot prove it (sign of `C_0 + c¹` against `λ + tc` in `(C_0+c¹)/(λ + (t+Θ)C_0 + tc)`
is not fixed), so `Q` is not claimed monotone for iso. Consequence for B5/B7: the iso tail "valid because every constant is
nondecreasing in δ" needs either (a) the engine to evaluate iso `QbN` at the tail bite and not infer it from monotonicity,
or (b) a rewrite that removes `1/C_ξL` (e.g. bound `Q̃_N/C_ξL` termwise: `Q̃_N ≤ C_ξL·(...) + (rest)`), or (c) a proved δ-monotonicity
hypothesis per package (a certified check). Plain step is unaffected. Signatures untouched.

## Checks
- `nice -n 5 lake build KAM.Sharp2.ModConstantsMono`: OK, no warnings from these files.
- `#print axioms` (probe) of all nine theorems: `[propext, Classical.choice, Quot.sound]`.
- Signature check: the signature block of `ModConstants` is contained verbatim in `ModConstants.lean`; `#check`s resolve.
- `scripts/lint_sources.sh`: module check PASS, frozen guard OK, the only error is the known ABI-scratch missing olean
  (`KAM.Frozen.Planetary.Theorems.FixedSunPlanetaryKAM`). Long-line notes only (verbatim signature lines and docstrings).
- Cross-check with `thresholds_v2.py::stageB` on package R1 (stage-0 bite δ₀, strip ρ, plain and iso, two sets of
  small-divisor constants; `t = 2·M1·σ_N^T σ_N + 1/10` as `stageB` defaults): `C_DK, C_0, C_ξL, Q̃_N, Q` EXACTLY equal as
  Fractions in all 4 cases ("R1 cross-check: all equal"). Plain step: 0 monotonicity violations in 500×9 random trials.
  Not covered by `stageB`: the optional `stage0` replacement of `C_E`, `C_DE` (blueprint: stage 0 only; for the engine/B6).

## Uncertainties / errata
- Blueprint `p2s2-modified.tex:145-146` and iso: monotonicity remark false for iso `QbN` (above).
- `StepIn` carries `t` (torsion cap) as an input; `stageB` derives `t = c_Th σ_N^T σ_N + slack`; the glue is B4/B6's.
- Python `stageB` evaluates `cTh = 2 M1`, `cDTh = 2 M2`, matching Lean's `2*M1`, `2*M2`.
