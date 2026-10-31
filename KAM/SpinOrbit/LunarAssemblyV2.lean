/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.CertV2
public import KAM.SpinOrbit.LunarAssemblySharpGen

/-!
# The lunar assembly through the v2 certifier, and its `N = 65` / R2 instance (SO-DATA3)

The statement of `lunar_barriers_of_sharpGen`, with the v2 certifier
`checkTorusCertificateV2 E` (any engine `E` and witnesses) in place of the sharp one:

* `lunar_barriers_of_v2Gen`: for `SoGraphCert α` over any lawful backend and any engine;
* `SoBackendV2 = CertFixed 96` and `lunar_barriers_of_R2V2`: the `N = 65` instance at the R2
  parameters through the combined engine `routeAV2`, where the Diophantine facts are discharged
  by `lunarRotFreq{Minus,Plus}N_isDiophantine_65`; the remaining hypotheses are signed data
  conclusions and rational band inequalities;
* `checkTorusCertificateV2_refined_of`: the v2 check at a refined-route witness from its parts
  (the landed sub-checks, the Ham claim, the frame majorants and `refinedCore`), so that the data
  modules can prove each part as a kernel computation of its own.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- **Theorem A through the v2 certifier, for any lawful backend and any engine**, parametric in
the band, the frequencies, the parameter packages and the time scale. -/
theorem lunar_barriers_of_v2Gen {α : Type} [CertArith α] [LawfulCertArith α] (E : EngineV2)
    (gL gU : SoGraphCert α) (PL PU : CertParams) (wL wU : E.Wit)
    (c κ γdL γdU lo hi pLo pHi : ℚ) (νL νU : ℝ) (hc0 : 0 < c)
    (hhamL : gL.base.ham = soRotHamExprScaled c) (hhamU : gU.base.ham = soRotHamExprScaled c)
    (hparL : gL.base.params = PL) (hparU : gU.base.params = PU)
    (hτL : PL.tau = 1) (hτU : PU.tau = 1) (hγL : PL.γ ≤ κ * γdL) (hγU : PU.γ ≤ κ * γdU)
    (hcL : checkTorusCertificateV2 E gL.base wL = true)
    (hcU : checkTorusCertificateV2 E gU.base wU = true)
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
  obtain ⟨BL⟩ := soRotBarrier_of_certV2 E gL hc0 hhamL hcL hgL hωL
    (hparL ▸ lunarRotFreq_isDiophantine_params hτL hγL hdL)
  obtain ⟨BU⟩ := soRotBarrier_of_certV2 E gU hc0 hhamU hcU hgU hωU
    (hparU ▸ lunarRotFreq_isDiophantine_params hτU hγU hdU)
  rw [hparL] at BL
  rw [hparU] at BU
  exact soBarriers_of_band_rat BL BU hbandL hbelow hlt habove hbandU

/-! ### The `N = 65` / R2 instance at `CertFixed 96` -/

/-- The mantissa precision of the v2 R2 backend (SO-V2PKG: 91 bits of data scale). -/
def soPrecisionV2 : ℕ := 96

/-- The v2 R2 backend: fixed point at 96 bits. -/
abbrev SoBackendV2 : Type := CertFixed soPrecisionV2

private theorem lunarR2_dio_form_v2 {ν : ℝ}
    (h : IsDiophantine ((lunarR2Kappa : ℝ) / 67) 1 (lunarRotFreq ν lunarR2Kappa)) :
    IsDiophantine ((lunarR2Kappa : ℝ) * ((1 / 67 : ℚ) : ℝ)) 1 (lunarRotFreq ν lunarR2Kappa) := by
  convert h using 1
  push_cast
  ring

/-- **Theorem A at `N = 65`, package R2, through the v2 certifier `routeAV2`, backend
`CertFixed 96`**, parametric in the data, the witnesses and the band: the hypotheses are the
signed data conclusions (`ham`, `params`, the v2 and graph checks, the frequency boxes) and the
rational band inequalities. -/
theorem lunar_barriers_of_R2V2 (gL gU : SoGraphCert SoBackendV2) (wL wU : routeAV2.Wit)
    (errL dispL errU dispU lo hi pLo pHi : ℚ)
    (hhamL : gL.base.ham = soRotHamExprScaled lunarR2TimeScale)
    (hhamU : gU.base.ham = soRotHamExprScaled lunarR2TimeScale)
    (hparL : gL.base.params = lunarR2 errL dispL) (hparU : gU.base.params = lunarR2 errU dispU)
    (hcL : checkTorusCertificateV2 routeAV2 gL.base wL = true)
    (hcU : checkTorusCertificateV2 routeAV2 gU.base wU = true)
    (hgL : checkSoGraph gL = true) (hgU : checkSoGraph gU = true)
    (hωL : FreqEncloses 2 gL.base.freqBox (lunarRotFreq (lunarNuMinusN 65) lunarR2Kappa))
    (hωU : FreqEncloses 2 gU.base.freqBox (lunarRotFreq (lunarNuPlusN 65) lunarR2Kappa))
    (hbandL : lo ≤ gL.pLo - dispL) (hbelow : gL.pHi + dispL < pLo) (hlt : pLo < pHi)
    (habove : pHi < gU.pLo - dispU) (hbandU : gU.pHi + dispU ≤ hi) :
    ∃ (Bm : SoBarrier lo hi) (Bp : SoBarrier lo hi),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < pLo) ∧ (∀ q φ, (pHi : ℝ) < Bp.P q φ) :=
  lunar_barriers_of_v2Gen routeAV2 gL gU (lunarR2 errL dispL) (lunarR2 errU dispU) wL wU
    lunarR2TimeScale lunarR2Kappa (1 / 67) (1 / 67) lo hi pLo pHi (lunarNuMinusN 65)
    (lunarNuPlusN 65) lunarR2TimeScale_pos hhamL hhamU hparL hparU rfl rfl
    (lunarR2_gamma_le errL dispL) (lunarR2_gamma_le errU dispU) hcL hcU hgL hgU hωL hωU
    (lunarR2_dio_form_v2 (lunarRotFreqMinusN_isDiophantine_65 lunarR2Kappa_pos))
    (lunarR2_dio_form_v2 (lunarRotFreqPlusN_isDiophantine_65 lunarR2Kappa_pos))
    hbandL hbelow hlt habove hbandU

/-! ### Sharding the v2 check at a refined-route witness -/

/-- The landed sub-checks of `checkTorusCertificateV2` from the seven checks. -/
theorem landedBase_check_of {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    (h1 : checkStatic c = true) (h2 : checkHamBounds c = true) (h3 : checkEmbedding c = true)
    (h4 : checkInvariance c = true) (h5 : checkEnergy c = true) (h6 : checkGram c = true)
    (h7 : checkTorsion c = true) : landedBase.check c = true := by
  simp only [landedBase, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- The v2 check at the refined-route witness `Sum.inr (Sum.inr w)` from its parts. -/
theorem checkTorusCertificateV2_refined_of {n : ℕ} {α : Type} [CertArith α]
    {c : TorusCertificate n α} {w : RefinedWit} (hb : landedBase.check c = true)
    (hH : checkHamClaim c w.R = true) (hF : checkFrameMajorants c (w.R.frame c.freqBox) = true)
    (hcore : refinedCore n c.params c.freqBox w = true) :
    checkTorusCertificateV2 routeAV2 c (Sum.inr (Sum.inr w)) = true := by
  simp only [checkTorusCertificateV2, checkV2With, Bool.and_eq_true]
  exact ⟨hb, by simp [routeAV2, EngineV2.orElse, routeARefined, refinedTest, hH, hF, hcore]⟩

end KAM.SpinOrbit
