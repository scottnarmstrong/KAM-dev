/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.LunarAssembly
public import KAM.SpinOrbit.Graph.CertSharp

/-!
# The lunar assembly through the sharp certifier, with the band as a parameter (SO-SHARPLINK)

The final results for arbitrary graph certificates `gL`, `gU`, parametric in everything the new
data fix (D36, D38): the band `[lo, hi]`, the frequencies `ν±` (any reals, with the Diophantine
facts `IsDiophantine (κ γ±) 1 (lunarRotFreq ν± κ)` as hypotheses), the parameter packages `PL`,
`PU` (used only through `τ = 1`, `γ ≤ κ γ±` and `disp`) and the time scale `c`.

* `soBarriers_of_band`: two barriers with separated bands inside `[lo, hi]` (pure band algebra).
* `lunar_barriers_of_sharp`: the two barriers from the sharp certifier
  (`soRotBarrier_of_certSharp`).
* `lunar_barriers_of_band`: the same from the old certifier (`soRotBarrier_of_cert`); the landed
  N = 40 / R1 / 3.3 % `lunar_barriers_of` is re-derived from it as `lunar_barriers_of_viaBand`.
* `lunar_spin_confinement_of_band`: confinement `|p(t) - 1| ≤ δ` for `1 - δ ≤ lo`, `hi ≤ 1 + δ`;
  the landed `lunar_spin_confinement_of` is re-derived as `lunar_spin_confinement_of_viaBand`.

Every hypothesis is a signed data conclusion (`ham`, `params`, the checks, the frequency boxes),
a Diophantine fact, or a rational inequality closed by `decide +kernel`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate KAM.CertificateSharp

/-- `IsDiophantine` is antitone in `γ`. -/
theorem isDiophantine_of_le_gamma {n : ℕ} {γ γ' τ : ℝ} {ω : Fin n → ℝ}
    (h : IsDiophantine γ' τ ω) (hγ : γ ≤ γ') : IsDiophantine γ τ ω := fun k hk =>
  (div_le_div_of_nonneg_right hγ
    (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) τ)).trans (h k hk)

/-- The certificate-form Diophantine premise from a Diophantine fact `(κ γd, 1)` for
`lunarRotFreq ν κ` and the package facts `τ = 1`, `γ ≤ κ γd`. -/
theorem lunarRotFreq_isDiophantine_params {P : CertParams} {κ γd : ℚ} {ν : ℝ}
    (hτ : P.tau = 1) (hγ : P.γ ≤ κ * γd)
    (hd : IsDiophantine ((κ : ℝ) * γd) 1 (lunarRotFreq ν κ)) :
    IsDiophantine (P.γ : ℝ) (P.tau : ℝ) (lunarRotFreq ν κ) := by
  rw [hτ, Nat.cast_one]
  exact isDiophantine_of_le_gamma hd (by exact_mod_cast hγ)

/-- Two barriers with bands `[aL, bL]` below `pLo < pHi` below `[aU, bU]`, all inside `[lo, hi]`,
give two barriers in `[lo, hi]` separated by the window `(pLo, pHi)`. -/
theorem soBarriers_of_band {aL bL aU bU : ℝ} {lo hi pLo pHi : ℚ}
    (BL : SoBarrier aL bL) (BU : SoBarrier aU bU) (hbandL : (lo : ℝ) ≤ aL) (hbelow : bL < pLo)
    (hlt : pLo < pHi) (habove : (pHi : ℝ) < aU) (hbandU : bU ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) := by
  have hl : (pLo : ℝ) < pHi := by exact_mod_cast hlt
  have hL0 := (BL.lower 0 0).trans (BL.upper 0 0)
  have hU0 := (BU.lower 0 0).trans (BU.upper 0 0)
  refine ⟨BL.widen hbandL (by linarith), BU.widen (by linarith) hbandU, fun q φ => ?_,
    fun q φ => ?_, fun q φ => ?_⟩
  · have := BL.upper q φ; have := BU.lower q φ
    show BL.P q φ < BU.P q φ
    linarith
  · have := BL.upper q φ
    show BL.P q φ < pLo
    linarith
  · have := BU.lower q φ
    show (pHi : ℝ) < BU.P q φ
    linarith

/-- The rational band facts of the data, cast to the reals for `soBarriers_of_band`. -/
theorem soBarriers_of_band_rat {pLoL pHiL dL pLoU pHiU dU lo hi pLo pHi : ℚ}
    (BL : SoBarrier ((pLoL : ℝ) - dL) ((pHiL : ℝ) + dL))
    (BU : SoBarrier ((pLoU : ℝ) - dU) ((pHiU : ℝ) + dU))
    (hbandL : lo ≤ pLoL - dL) (hbelow : pHiL + dL < pLo) (hlt : pLo < pHi)
    (habove : pHi < pLoU - dU) (hbandU : pHiU + dU ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) :=
  soBarriers_of_band BL BU (by exact_mod_cast hbandL) (by exact_mod_cast hbelow) hlt
    (by exact_mod_cast habove) (by exact_mod_cast hbandU)

/-- **Theorem A through the sharp certifier, parametric in the band, the frequencies, the
parameter packages and the time scale.** -/
theorem lunar_barriers_of_sharp (gL gU : SoGraphCert SoBackend) (PL PU : CertParams)
    (c κ γdL γdU lo hi pLo pHi : ℚ) (νL νU : ℝ) (hc0 : 0 < c)
    (hhamL : gL.base.ham = soRotHamExprScaled c) (hhamU : gU.base.ham = soRotHamExprScaled c)
    (hparL : gL.base.params = PL) (hparU : gU.base.params = PU)
    (hτL : PL.tau = 1) (hτU : PU.tau = 1) (hγL : PL.γ ≤ κ * γdL) (hγU : PU.γ ≤ κ * γdU)
    (hcL : checkTorusCertificateSharp gL.base = true)
    (hcU : checkTorusCertificateSharp gU.base = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq νL κ))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq νU κ))
    (hdL : IsDiophantine ((κ : ℝ) * γdL) 1 (lunarRotFreq νL κ))
    (hdU : IsDiophantine ((κ : ℝ) * γdU) 1 (lunarRotFreq νU κ))
    (hbandL : lo ≤ gL.pLo - PL.disp) (hbelow : gL.pHi + PL.disp < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - PU.disp) (hbandU : gU.pHi + PU.disp ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) := by
  obtain ⟨BL⟩ := soRotBarrier_of_certSharp gL hc0 hhamL hcL hgL hωL
    (hparL ▸ lunarRotFreq_isDiophantine_params hτL hγL hdL)
  obtain ⟨BU⟩ := soRotBarrier_of_certSharp gU hc0 hhamU hcU hgU hωU
    (hparU ▸ lunarRotFreq_isDiophantine_params hτU hγU hdU)
  rw [hparL] at BL
  rw [hparU] at BU
  exact soBarriers_of_band_rat BL BU hbandL hbelow hlt habove hbandU

/-- Theorem A through the old certifier, with the same parameters as `lunar_barriers_of_sharp`
(the sanity bridge to the landed `lunar_barriers_of`). -/
theorem lunar_barriers_of_band (gL gU : SoGraphCert SoBackend) (PL PU : CertParams)
    (c κ γdL γdU lo hi pLo pHi : ℚ) (νL νU : ℝ) (hc0 : 0 < c)
    (hhamL : gL.base.ham = soRotHamExprScaled c) (hhamU : gU.base.ham = soRotHamExprScaled c)
    (hparL : gL.base.params = PL) (hparU : gU.base.params = PU)
    (hτL : PL.tau = 1) (hτU : PU.tau = 1) (hγL : PL.γ ≤ κ * γdL) (hγU : PU.γ ≤ κ * γdU)
    (hcL : checkTorusCertificate gL.base = true) (hcU : checkTorusCertificate gU.base = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq νL κ))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq νU κ))
    (hdL : IsDiophantine ((κ : ℝ) * γdL) 1 (lunarRotFreq νL κ))
    (hdU : IsDiophantine ((κ : ℝ) * γdU) 1 (lunarRotFreq νU κ))
    (hbandL : lo ≤ gL.pLo - PL.disp) (hbelow : gL.pHi + PL.disp < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - PU.disp) (hbandU : gU.pHi + PU.disp ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) := by
  obtain ⟨BL⟩ := soRotBarrier_of_cert gL hc0 hhamL hcL hgL hωL
    (hparL ▸ lunarRotFreq_isDiophantine_params hτL hγL hdL)
  obtain ⟨BU⟩ := soRotBarrier_of_cert gU hc0 hhamU hcU hgU hωU
    (hparU ▸ lunarRotFreq_isDiophantine_params hτU hγU hdU)
  rw [hparL] at BL
  rw [hparU] at BU
  exact soBarriers_of_band_rat BL BU hbandL hbelow hlt habove hbandU

/-- **Theorem B, parametric in the band and the window**: a solution started in the window stays
in `|p - 1| ≤ δ` whenever the band `[lo, hi]` lies in `[1 - δ, 1 + δ]`. -/
theorem lunar_spin_confinement_of_band (lo hi δ pLo pHi : ℚ) (hlo : 1 - δ ≤ lo)
    (hhi : hi ≤ 1 + δ)
    (hB : ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ))
    (q₀ p₀ φ₀ : ℝ) (hp : (pLo : ℝ) < p₀ ∧ p₀ < pHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ δ) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  obtain ⟨Bm, Bp, -, hm, hpB⟩ := hB
  obtain ⟨z, hz, hconf, huniq⟩ := so_confinement Bm Bp (q₀, p₀, φ₀)
    ((hm q₀ φ₀).trans hp.1) (hp.2.trans (hpB q₀ φ₀))
  refine ⟨z, hz, fun t => ?_, huniq⟩
  have hlo' : 1 - (δ : ℝ) ≤ lo := by exact_mod_cast hlo
  have hhi' : (hi : ℝ) ≤ 1 + δ := by exact_mod_cast hhi
  have h1 := Bm.lower (z t).1 (z t).2.2
  have h2 := Bp.upper (z t).1 (z t).2.2
  obtain ⟨c1, c2⟩ := hconf t
  rw [abs_le]
  constructor <;> linarith

/-! ### Sanity: the landed N = 40 / R1 / 3.3 % results as corollaries -/

private theorem lunarR1Kappa_pos' : 0 < lunarR1Kappa := by decide +kernel

private theorem lunarR1TimeScale_pos' : 0 < lunarR1TimeScale := by decide +kernel

private theorem cast_967 : ((967 / 1000 : ℚ) : ℝ) = 967 / 1000 := by norm_num

private theorem cast_1033 : ((1033 / 1000 : ℚ) : ℝ) = 1033 / 1000 := by norm_num

private theorem lunarR1_gamma_le (err disp : ℚ) :
    (lunarR1 err disp).γ ≤ lunarR1Kappa * (1 / 42) :=
  le_of_eq (by simp only [lunarR1]; ring)

private theorem lunarR1_dio_form {ν : ℝ}
    (h : IsDiophantine ((lunarR1Kappa : ℝ) / 42) 1 (lunarRotFreq ν lunarR1Kappa)) :
    IsDiophantine ((lunarR1Kappa : ℝ) * ((1 / 42 : ℚ) : ℝ)) 1 (lunarRotFreq ν lunarR1Kappa) := by
  convert h using 1
  push_cast
  ring

/-- The landed `lunar_barriers_of` (statement verbatim), re-derived from
`lunar_barriers_of_band`. -/
theorem lunar_barriers_of_viaBand (gL gU : SoGraphCert SoBackend)
    (errL dispL errU dispU pLo pHi : ℚ)
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
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) := by
  have h := lunar_barriers_of_band gL gU (lunarR1 errL dispL) (lunarR1 errU dispU)
    lunarR1TimeScale lunarR1Kappa (1 / 42) (1 / 42) (967 / 1000) (1033 / 1000) pLo pHi
    lunarNuMinus lunarNuPlus lunarR1TimeScale_pos' hhamL hhamU hparL hparU rfl rfl
    (lunarR1_gamma_le errL dispL) (lunarR1_gamma_le errU dispU) hcL hcU hgL hgU hωL hωU
    (lunarR1_dio_form (lunarRotFreqMinus_isDiophantine lunarR1Kappa_pos'))
    (lunarR1_dio_form (lunarRotFreqPlus_isDiophantine lunarR1Kappa_pos'))
    hbandL hbelow hlt habove hbandU
  rwa [cast_967, cast_1033] at h

/-- The landed `lunar_spin_confinement_of` (statement verbatim), re-derived from
`lunar_spin_confinement_of_band`. -/
theorem lunar_spin_confinement_of_viaBand (pLo pHi : ℚ)
    (hB : ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000))
      (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ))
    (q₀ p₀ φ₀ : ℝ) (hp : (pLo : ℝ) < p₀ ∧ p₀ < pHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 33 / 1000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  have h := lunar_spin_confinement_of_band (967 / 1000) (1033 / 1000) (33 / 1000) pLo pHi
    (by norm_num) (by norm_num) (by rwa [cast_967, cast_1033]) q₀ p₀ φ₀ hp
  rwa [show ((33 / 1000 : ℚ) : ℝ) = 33 / 1000 by norm_num] at h

end KAM.SpinOrbit
