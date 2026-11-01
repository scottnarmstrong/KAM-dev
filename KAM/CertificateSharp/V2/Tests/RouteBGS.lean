/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteBGS
public import KAM.CertificateSharp.V2.Tests.RouteBE
public import KAM.CertificateSharp.V2.Tests.RouteBLN
public import KAM.CertificateSharp.V2.Tests.SiteSign

/-!
# Route B with general sites on the toys `toyB` and `toyBNeg`

* **`toyB` (T2 at `ρ = 1`).** The images of the witnesses of `routeBRefinedLN` and `routeBRefinedE`
  pass `routeBRefinedGSLN` and `routeBRefinedGSE` (by `rfl` from their landed tests, through
  `checkTorusCertificateV2_routeBRefinedGSLN_ofLN`, `…GSE_ofE`). The witness `toyBGain`, between
  the two thresholds, passes the energy-row engine and is rejected without it, as in
  `Tests/RouteBE.lean`.
* **`toyBNeg` (T2 with `H ↦ -H`, `ω ↦ -ω`, at `ρ = 1`).** The last coordinate of the box is
  `-1/2`, so `clockOk` rejects the landed sites and `routeBRefinedLN` rejects the certificate. With
  the sites on the reflected box (`neg = true`) both new engines accept it, and
  `toyBNeg_torus` gives the torus at `-(ν₋/2, 1/2)`. The wrong sign is rejected.

Every new check is a kernel computation (`decide +kernel`); the whole certifier is assembled from
its parts (`checkTorusCertificateV2_routeBRefinedGSLN_of`), so the landed sub-checks run once.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-! ### `toyB`: the images of the landed witnesses -/

/-- The image of the refined route-B witness of `toyB`. -/
def toyBGS : RefinedBWitGS := ⟨RefinedBWitG.ofRefined toyRefinedBWit, false, toyB.freqBox⟩

theorem toyB_refinedBGSLN_passes :
    checkTorusCertificateV2 routeBRefinedGSLN toyB toyBGS = true :=
  (checkTorusCertificateV2_routeBRefinedGSLN_ofLN toyB toyRefinedBWit).trans
    toyB_refinedBLN_passes

theorem toyB_refinedBGSE_passes : checkTorusCertificateV2 routeBRefinedGSE toyB toyBGS = true :=
  (checkTorusCertificateV2_routeBRefinedGSE_ofE toyB toyRefinedBWit).trans toyB_refinedBE_passes

/-- The image of `toyBGain`, between the thresholds of `y₀ = M s_N` and `y₀ = dh s_N`. -/
def toyBGainGS : RefinedBWitGS := ⟨RefinedBWitG.ofRefined toyBGain, false, toyB.freqBox⟩

theorem toyB_refinedBGSE_gain_passes :
    checkTorusCertificateV2 routeBRefinedGSE toyB toyBGainGS = true :=
  (checkTorusCertificateV2_routeBRefinedGSE_ofE toyB toyBGain).trans toyB_refinedBE_gain_passes

theorem toyB_refinedBGSLN_gain_rejects :
    checkTorusCertificateV2 routeBRefinedGSLN toyB toyBGainGS = false :=
  (checkTorusCertificateV2_routeBRefinedGSLN_ofLN toyB toyBGain).trans
    toyB_refinedBLN_gain_rejects

/-! ### `toyBNeg`: the negative clock on route B's strip -/

/-- T2 with the sign of `H` and of the frequency changed, on the strip `ρ = 1`. -/
def toyBNeg : TorusCertificate 2 ℚ := { toyNeg with params := toyB.params, weight := toyB.weight }

/-- The sites on the reflected box (T2's box). -/
def toyBNegWit : RefinedBWitGS := ⟨RefinedBWitG.ofRefined toyRefinedBWit, true, toyCert2.freqBox⟩

/-- The wrong sign: the sites on T2's box, read at `+ω*`. -/
def toyBNegWrong : RefinedBWitGS :=
  ⟨RefinedBWitG.ofRefined toyRefinedBWit, false, toyCert2.freqBox⟩

theorem toyBNeg_base : landedBase.check toyBNeg = true := by decide +kernel

theorem toyBNeg_hamClaim : checkHamClaim toyBNeg toyRefinedBWit.R = true := by decide +kernel

theorem toyBNeg_frameLN :
    checkFrameLN toyBNeg toyRefinedBWit.R.bL toyRefinedBWit.R.bN toyRefinedBWit.R.bNt = true := by
  decide +kernel

/-- The landed sites reject the negative clock. -/
theorem toyBNeg_core_rejects :
    refinedBCore 2 toyBNeg.params toyBNeg.freqBox toyRefinedBWit = false := by decide +kernel

theorem toyBNeg_refinedBLN_rejects :
    checkTorusCertificateV2 routeBRefinedLN toyBNeg toyRefinedBWit = false := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedLN, refinedBLNTest,
    toyBNeg_core_rejects, Bool.and_false]

theorem toyBNeg_coreGSLN :
    refinedBCoreGS 2 toyBNeg.params toyBNeg.freqBox toyBNeg.params.M toyBNegWit = true := by
  decide +kernel

theorem toyBNeg_coreGSE :
    refinedBCoreGS 2 toyBNeg.params toyBNeg.freqBox toyRefinedBWit.R.dh toyBNegWit = true := by
  decide +kernel

theorem toyBNeg_coreGS_wrong_rejects :
    refinedBCoreGS 2 toyBNeg.params toyBNeg.freqBox toyBNeg.params.M toyBNegWrong = false := by
  decide +kernel

/-- **The negative clock through route B with sign-tolerant sites**, without the torsion
majorant. -/
theorem toyBNeg_refinedBGSLN_passes :
    checkTorusCertificateV2 routeBRefinedGSLN toyBNeg toyBNegWit = true :=
  checkTorusCertificateV2_routeBRefinedGSLN_of toyBNeg_base toyBNeg_hamClaim toyBNeg_frameLN
    toyBNeg_coreGSLN

/-- **The negative clock through route B with sign-tolerant sites and the energy row.** -/
theorem toyBNeg_refinedBGSE_passes :
    checkTorusCertificateV2 routeBRefinedGSE toyBNeg toyBNegWit = true :=
  checkTorusCertificateV2_routeBRefinedGSE_of toyBNeg_base toyBNeg_hamClaim toyBNeg_frameLN
    toyBNeg_coreGSE

theorem toyBNeg_dio : IsDiophantine ((toyBNeg.params.γ : ℚ) : ℝ) ((toyBNeg.params.tau : ℕ) : ℝ)
    (-![lunarNuMinus / 2, 1 / 2]) := by
  have h : ((toyBNeg.params.γ : ℚ) : ℝ) = 1 / 42 := by
    rw [show toyBNeg.params.γ = 1 / 42 by decide +kernel]; norm_num
  have ht : ((toyBNeg.params.tau : ℕ) : ℝ) = 1 := by
    rw [show toyBNeg.params.tau = 1 by decide +kernel]; norm_num
  rw [h, ht]
  exact isDiophantine_neg lunarNuMinus_half_isDiophantine

/-- **The toy torus at the negative frequency through route B**, with sign-tolerant sites and the
energy row. -/
theorem toyBNeg_torus : CertifiedTorus toyBNeg (-![lunarNuMinus / 2, 1 / 2]) :=
  checkTorusCertificateV2_routeBRefinedGSE_sound toyBNeg_refinedBGSE_passes
    (freqEncloses_negBox toyCert2_freq) toyBNeg_dio

end KAM.CertificateSharp.V2

end
