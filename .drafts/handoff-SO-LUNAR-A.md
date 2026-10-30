# Handoff SO-LUNAR-A (branch inp-solunara)

## Files
- NEW `KAM/SpinOrbit/LunarAssembly.lean` (129 lines, module, ≤100 cols). Defines `soPrecision := 320`,
  `SoBackend := CertFixed soPrecision` (as signed; they did not exist), `SoBarrier.widen`, and the two theorems.
  No data constants, no sorry/placeholder.

## Statements
```lean
theorem lunar_barriers_of (gL gU : SoGraphCert SoBackend) (errL dispL errU dispU pLo pHi : ℚ)
    (hhamL : gL.base.ham = soRotHamExprScaled lunarR1TimeScale)
    (hhamU : gU.base.ham = soRotHamExprScaled lunarR1TimeScale)
    (hparL : gL.base.params = lunarR1 errL dispL) (hparU : gU.base.params = lunarR1 errU dispU)
    (hcL : checkTorusCertificate gL.base = true) (hcU : checkTorusCertificate gU.base = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq lunarNuMinus lunarR1Kappa))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq lunarNuPlus lunarR1Kappa))
    (hbandL : 967 / 1000 ≤ gL.pLo - dispL) (hbelow : gL.pHi + dispL < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - dispU) (hbandU : gU.pHi + dispU ≤ 1033 / 1000) :
    ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000)) (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ)

theorem lunar_spin_confinement_of (pLo pHi : ℚ)
    (hB : ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000))
      (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ))
    (q₀ p₀ φ₀ : ℝ) (hp : (pLo : ℝ) < p₀ ∧ p₀ < pHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 33 / 1000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z
```
Instantiation by SO-DATA: `lunar_barriers_of lunarLowerCert lunarUpperCert lunarLowerErr lunarLowerDisp
lunarUpperErr lunarUpperDisp lunarPLo lunarPHi <*_ham> <*_params> <*_passes> <*Graph_passes> <*_freq>
<5 inequalities>`, then `lunar_spin_confinement_of lunarPLo lunarPHi lunar_barriers`.

## Approach / consumed lemmas
`soRotBarrier_of_cert` (Graph/Cert, c = lunarR1TimeScale > 0 by `decide +kernel`); Diophantine input
`lunarRotFreqMinus_isDiophantine` / `lunarRotFreqPlus_isDiophantine` (RotFreq; built on
`lunarNu{Minus,Plus}_rot_isDiophantine` in Certificate/DiophantineTransfer) at γ = κ/42, τ = 1 with κ =
lunarR1Kappa > 0 (`decide +kernel`); params rewritten via `lunarR1` (γ = lunarR1Kappa/42, tau = 1, disp).
Band widening by new `SoBarrier.widen`. Theorem B: `so_confinement` (Barrier.lean), which itself uses
`so_global_exists_unique`; |p-1| ≤ 33/1000 from the barrier bands.

## Data inequalities SO-DATA must satisfy (ℚ, decidable by `decide +kernel`)
With dL = lunarLowerDisp = lunarLowerCert.base.params.disp, dU likewise:
1. `967/1000 ≤ lunarLowerCert.pLo - dL`
2. `lunarLowerCert.pHi + dL < lunarPLo`
3. `lunarPLo < lunarPHi` (= signed `lunarPLo_lt_lunarPHi`)
4. `lunarPHi < lunarUpperCert.pLo - dU`
5. `lunarUpperCert.pHi + dU ≤ 1033/1000`
Minimality: the brief's other band facts (`gL.pHi + dL ≤ 1033/1000`, `967/1000 ≤ gU.pLo - dU`) are DROPPED;
they follow from 1–5 plus `pLo_g - d ≤ pHi_g + d` (read off a barrier value). No extra premise was added.
The err parameters enter only through the params equations (unconstrained).

## Checks
- `inp_lake_build.sh … KAM.SpinOrbit.LunarAssembly`: Build completed successfully (3333 jobs); no warnings
  in LunarAssembly.
- `scripts/lint_sources.sh`: check_lean_modules PASS (1383 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `main_shortname_check.py . KAM.SpinOrbit.LunarAssembly`: OK (rc 0).
- No line > 100 columns; no heartbeat overrides.

## Axioms
Both theorems: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
- `soPrecision`, `SoBackend` defined here as signed (§I.6); if SO-DATA's module also defines them, it must
  import this one instead (or move them). No suspected source errata.
