/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.LunarAssemblySharp
public import KAM.SpinOrbit.LunarParamsR2

/-!
# The sharp lunar assembly for any lawful backend, and its `N = 65` / R2 instance (SO-R2)

`lunar_barriers_of_sharp` is pinned to `SoBackend = CertFixed 320`; the `N = 65` data use
`CertFixed 160` (SO-GEN3: 158 bits).

* `lunar_barriers_of_sharpGen`: the same statement for `SoGraphCert α` over any
  `[CertArith α] [LawfulCertArith α]`; the landed theorem is re-derived from it as
  `lunar_barriers_of_sharp_viaGen`.
* `SoBackendR2 = CertFixed 160` and `lunar_barriers_of_R2`: the `N = 65` instance at the R2
  parameters (`ν± = lunarNu{Minus,Plus}N 65`, `κ = lunarR2Kappa`, `γ = κ/67`, `c = 2`), where the
  Diophantine facts are discharged by `lunarRotFreq{Minus,Plus}N_isDiophantine_65`; the
  remaining hypotheses are signed data conclusions and rational band inequalities.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate KAM.CertificateSharp

/-- **Theorem A through the sharp certifier, for any lawful backend**, parametric in the band,
the frequencies, the parameter packages and the time scale. -/
theorem lunar_barriers_of_sharpGen {α : Type} [CertArith α] [LawfulCertArith α]
    (gL gU : SoGraphCert α) (PL PU : CertParams)
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

/-- The landed `lunar_barriers_of_sharp` (statement verbatim), re-derived from
`lunar_barriers_of_sharpGen` at `α = SoBackend`. -/
theorem lunar_barriers_of_sharp_viaGen (gL gU : SoGraphCert SoBackend) (PL PU : CertParams)
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
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) :=
  lunar_barriers_of_sharpGen gL gU PL PU c κ γdL γdU lo hi pLo pHi νL νU hc0 hhamL hhamU hparL
    hparU hτL hτU hγL hγU hcL hcU hgL hgU hωL hωU hdL hdU hbandL hbelow hlt habove hbandU

/-! ### The `N = 65` / R2 instance at `CertFixed 160` -/

/-- The mantissa precision of the R2 backend (SO-GEN3: 158 bits needed). -/
def soPrecisionR2 : ℕ := 160

/-- The R2 backend: fixed point at 160 bits. -/
abbrev SoBackendR2 : Type := CertFixed soPrecisionR2

private theorem lunarR2_dio_form {ν : ℝ}
    (h : IsDiophantine ((lunarR2Kappa : ℝ) / 67) 1 (lunarRotFreq ν lunarR2Kappa)) :
    IsDiophantine ((lunarR2Kappa : ℝ) * ((1 / 67 : ℚ) : ℝ)) 1 (lunarRotFreq ν lunarR2Kappa) := by
  convert h using 1
  push_cast
  ring

/-- **Theorem A at `N = 65`, package R2, backend `CertFixed 160`**, parametric in the data and
the band: the hypotheses are the signed data conclusions (`ham`, `params`, the sharp and graph
checks, the frequency boxes) and the rational band inequalities. -/
theorem lunar_barriers_of_R2 (gL gU : SoGraphCert SoBackendR2)
    (errL dispL errU dispU lo hi pLo pHi : ℚ)
    (hhamL : gL.base.ham = soRotHamExprScaled lunarR2TimeScale)
    (hhamU : gU.base.ham = soRotHamExprScaled lunarR2TimeScale)
    (hparL : gL.base.params = lunarR2 errL dispL) (hparU : gU.base.params = lunarR2 errU dispU)
    (hcL : checkTorusCertificateSharp gL.base = true)
    (hcU : checkTorusCertificateSharp gU.base = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq (lunarNuMinusN 65) lunarR2Kappa))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq (lunarNuPlusN 65) lunarR2Kappa))
    (hbandL : lo ≤ gL.pLo - dispL) (hbelow : gL.pHi + dispL < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - dispU) (hbandU : gU.pHi + dispU ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) :=
  lunar_barriers_of_sharpGen gL gU (lunarR2 errL dispL) (lunarR2 errU dispU) lunarR2TimeScale
    lunarR2Kappa (1 / 67) (1 / 67) lo hi pLo pHi (lunarNuMinusN 65) (lunarNuPlusN 65)
    lunarR2TimeScale_pos hhamL hhamU hparL hparU rfl rfl (lunarR2_gamma_le errL dispL)
    (lunarR2_gamma_le errU dispU) hcL hcU hgL hgU hωL hωU
    (lunarR2_dio_form (lunarRotFreqMinusN_isDiophantine_65 lunarR2Kappa_pos))
    (lunarR2_dio_form (lunarRotFreqPlusN_isDiophantine_65 lunarR2Kappa_pos))
    hbandL hbelow hlt habove hbandU

end KAM.SpinOrbit
