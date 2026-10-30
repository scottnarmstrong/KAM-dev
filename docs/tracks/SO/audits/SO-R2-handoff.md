# Handoff SO-R2: the N = 65 parameter package R2 in Lean, and a backend-generic sharp assembly

Branch `inp-sor2` (worktree /root/code/KAM-inp-sor2). No landed declaration changed; no frozen file touched.

## Files (new)
- `KAM/SpinOrbit/LunarParamsR2.lean` (204 lines): package R2 and kernel pre-checks.
- `KAM/SpinOrbit/LunarAssemblySharpGen.lean` (123 lines): backend-generic sharp assembly, `SoBackendR2`, the
  N = 65 / R2 instance.
- `KAM.lean` NOT regenerated (rule 10); it needs `scripts/gen_root_imports.py` for the two new modules.

## The package (`lunarR2 (err disp : ℚ) : CertParams`), exactly SO-GEN3's g3_r2.py `R2(65)`
`lunarR2TimeScale = 2`, `lunarR2Scalar = 1 + 1/10^6`, `lunarR2Kappa = c/s = 2000000/1000001` (`lunarR2Kappa_eq`);
τ = 1, ρ = 1/140, ρ∞ = 1/140000, M = 54/25, σK = 1873/1000, σB = 2689/500, σT = 13/25, μ = 1/160,
γ̄ = γ = κ/67, σω = 2, ν = 1/10^6, s = 1 + 10^-6, E₀ = 0, err, disp.

## Pre-check results (all `decide +kernel`)
- `lunarR2_staticCore` (via `lunarR2_staticCore_zero`): `lunarR1StaticCore (lunarR2 err disp) = true` for all
  err, disp (the R1 helper is parameter-generic: 2 ≤ τ+1, 0 < ρ∞ < ρ, positivities, 1 < s < σω, 0 < γ ≤ γ̄);
  `lunarR2_err_nonneg` for `0 ≤ err`.
- Sharp test: `lunarR2SharpCore p` is the body of `sharpTest` at n = 2 (`sharpTest_eq_lunarR2SharpCore : sharpTest c
  = lunarR2SharpCore c.params`, by `rfl`; `sharpTest_of_lunarR2SharpCore`).
  `lunarR2_sharpCore_budgets`: both inequalities pass at
  - lower: err = 69/10^36 = 6.9e-35 (budget 6.8e-35), disp = 27/10^20 (needed 2.643e-19);
  - upper: err = 82/10^36 = 8.2e-35 (budget 8.17e-35), disp = 32/10^20 (needed 3.141e-19).
- Threshold (exact rational, SO-GEN3 `sharp_q.sharp`): **1.48831e-32 = 10^-31.8273**, active branch E.
  `lunarR2_sharp_C1`: C₁♯ passes at err = 1.48e-32; `lunarR2_sharp_C1_fails`: fails at err = 1.49e-32
  (= 10^-31.827; sharp to a factor 1.007). Disp coefficient max(C₂♯, C₃♯)/(γ²ρ²) = 3.8305e15 = 10^15.583.
  Headroom at the budgets: err/threshold = 10^-2.34 (lower), 10^-2.26 (upper); at the "just above" values
  10^-2.334 / 10^-2.259.
  Note: SO-GEN3's data disp 3.13e-19 for the upper torus at err 8.17e-35 needs 3.1295e-19 (margin 1.6e-4
  relative) — passes, but the "×1.001" in g3_r2's printout would give 3.133e-19; the data generator should not
  round disp down.
- Frequency boxes (algFreq form of `lunarRotFreq{Minus,Plus}N_eq` at N = 65, D = 8318, m = 129):
  `lunarR2MinusCoeffs`, `lunarR2PlusCoeffs`; `lunarR2Box coeffs` = (centre, radius) of the interval evaluation at
  √5 ∈ [2236067, 2236069]/10^6 (`lunarR2_sqrtFive_mem`, proved). `lunarR2_checkAlgBox` (kernel), and
  `lunarR2Box_minus_encloses` / `lunarR2Box_plus_encloses`: `FreqEncloses 2 (lunarR2Box …) (lunarRotFreq
  (lunarNu{Minus,Plus}N 65) lunarR2Kappa)` (real theorems, via `algFreq_encloses`).
- Ray margins `lunarR2_rayMargins`: 0 < L, ν ≤ (s−1)L, ν ≤ (σω−s)L for both boxes; `lunarR2Box_normLo`: L = κ
  exactly on both (coordinate 1). Margins: (s−1)L − ν = 10^-6·κ − 10^-6 ≈ 1.0e-6 (≈ ν; factor 2.0), (σω−s)L − ν
  ≈ 2.0 (κ(1 − 10^-6) − 10^-6).
- SO-DION bound `lunarR2_gamma_le : (lunarR2 err disp).γ ≤ lunarR2Kappa * (1/67)` (equality, by `ring`).

## Generic assembly
```
theorem lunar_barriers_of_sharpGen {α : Type} [CertArith α] [LawfulCertArith α]
    (gL gU : SoGraphCert α) (PL PU : CertParams) (c κ γdL γdU lo hi pLo pHi : ℚ) (νL νU : ℝ) ...
```
hypotheses and conclusion verbatim those of the landed `lunar_barriers_of_sharp` with `SoBackend` replaced by `α`.
The landed theorem is re-derived as `lunar_barriers_of_sharp_viaGen` (statement verbatim).
Also: `soPrecisionR2 : ℕ := 160`, `abbrev SoBackendR2 := CertFixed soPrecisionR2`, and
```
theorem lunar_barriers_of_R2 (gL gU : SoGraphCert SoBackendR2) (errL dispL errU dispU lo hi pLo pHi : ℚ)
    (hhamL/U : g.base.ham = soRotHamExprScaled lunarR2TimeScale)
    (hparL/U : g.base.params = lunarR2 err disp)
    (hcL/U : checkTorusCertificateSharp g.base = true) (hgL/U : checkSoGraph g = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq (lunarNuMinusN 65) lunarR2Kappa))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq (lunarNuPlusN 65) lunarR2Kappa))
    (hbandL : lo ≤ gL.pLo - dispL) (hbelow : gL.pHi + dispL < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - dispU) (hbandU : gU.pHi + dispU ≤ hi) :
    ∃ Bm Bp : SoBarrier lo hi, (∀ q φ, Bm.P q φ < Bp.P q φ) ∧ (∀ q φ, Bm.P q φ < pLo) ∧
      (∀ q φ, (pHi : ℝ) < Bp.P q φ)
```
Diophantine facts discharged by `lunarRotFreq{Minus,Plus}N_isDiophantine_65 lunarR2Kappa_pos`; τ = 1 by `rfl`.
Only data conclusions and rational band inequalities remain as hypotheses.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-sor2 KAM.SpinOrbit.LunarParamsR2 KAM.SpinOrbit.LunarAssemblySharpGen`:
  `✔ Built KAM.SpinOrbit.LunarParamsR2 (4.0s)`, `✔ Built KAM.SpinOrbit.LunarAssemblySharpGen (3.2s)`,
  `Build completed successfully (3402 jobs).` No warnings in the new files.
- `sh scripts/lint_sources.sh`: exit 1 with the single failure `KAM.lean is out of date; run
  scripts/gen_root_imports.py` (expected: two new modules; rule 10 forbids me to regenerate). Otherwise
  `check_lean_modules: PASS (1462 Lean files)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (146 frozen declarations)`.
- `main_shortname_check.py … LunarParamsR2 LunarAssemblySharpGen`: `short-name check OK (no reused public short
  name)`, exit 0 (it printed `fatal: Not a valid object name inp-sogen3` twice — a git lookup of a branch absent
  from this worktree; harmless).
- All lines ≤ 100 columns; no heartbeat options; no sorry/axiom.

## Axioms
`lunar_barriers_of_sharpGen`, `lunar_barriers_of_sharp_viaGen`, `lunar_barriers_of_R2`,
`lunarR2_sharpCore_budgets`, `lunarR2_sharp_C1`, `lunarR2_sharp_C1_fails`, `lunarR2_rayMargins`,
`lunarR2Box_{minus,plus}_encloses`, `lunarR2_staticCore`, `lunarR2_gamma_le`, `lunarR2Box_normLo`,
`sharpTest_of_lunarR2SharpCore`: all `[propext, Classical.choice, Quot.sound]`.

## Uncertainties / design signals
- None on heartbeats: all kernel checks elaborate in seconds.
- The pre-check box `lunarR2Box` is my own (√5 to 6 digits); the data's emitted `freqBox` may differ, so `hω`
  remains a data hypothesis in `lunar_barriers_of_R2` (the box theorems show the frequencies are enclosable and
  the ray margins hold with L = κ).
- `lunarR1StaticCore` is reused for R2 (it is parameter-generic despite its name) rather than duplicated.

## Errata / deviations
- No defect found in the pinned sources. Minor note on SO-GEN3 (not an erratum of a pinned source): the upper
  torus disp 3.13e-19 is only 1.6e-4 relative above the required 3.1295e-19 at err 8.17e-35; the report's "×1.001"
  rule would give 3.133e-19.
- Deviation: the "just above the budgets" checks use err 6.9e-35 / 8.2e-35 with disp 2.7e-19 / 3.2e-19.

AUDIT FOCUS: (1) lunarR2 is exactly SO-GEN3's package R2 (docs/tracks/SO/studies/SO-GEN3.md 'Full study N = 65' and scripts/spin_orbit/g3_r2.py on inp), field by field; (2) the sharp pre-checks really instantiate the landed `sharpTest` (sharpTest_eq_lunarR2SharpCore by rfl) and are non-vacuous (pass just below, fail just above the threshold); the threshold value 10^-31.827; (3) the frequency boxes really enclose lunarRotFreq (lunarNu{Minus,Plus}N 65) lunarR2Kappa (√5 enclosure, algFreq_encloses), and the ray margins and lunarR2_gamma_le are what checkStatic and the SO-DION Diophantine facts need; (4) lunar_barriers_of_sharpGen has hypotheses and conclusion verbatim those of the landed lunar_barriers_of_sharp with SoBackend generalized to any lawful backend α, and lunar_barriers_of_R2 is a faithful instance (the Diophantine facts discharged by the landed SO-DION lemmas, nothing smuggled); (5) no landed declaration changed; names, kernel replay, axioms, lint.
