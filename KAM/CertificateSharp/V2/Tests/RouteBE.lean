/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAllE
public import KAM.CertificateSharp.V2.Tests.RouteBToy

/-!
# Route B with the gradient bound in the energy row, in the kernel, on `toyB`

`toyB` has `M = 297/100` and `dh = 2`, so `y₀` falls from `M s_N = 3.15` to `dh s_N = 2.12`.

* an ordinary refined witness passes `routeBRefinedE`, by itself and inside `routeV2AllE`;
* `toyBGain`, at `X⋆ = 27·10⁻⁶` and the local budget `10⁻⁴`, passes `routeBRefinedE` and is rejected by
  `routeBRefined` and `routeBRefinedLN`: the old `y₀` puts `X⋆` above the threshold;
* `toyBLowDh`, the ordinary witness with `dh` understated, is rejected, although `refinedBCoreE`
  alone accepts it: `checkHamClaim` is what rejects it;
* the toy torus through both engines, at `toyBGain`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- A witness between the two thresholds. -/
def toyBGain : RefinedBWit :=
  { toyRefinedBWit with
    core := { toyRefinedBWit.core with Xs := 27 / 10 ^ 6, bF := 1 / 10 ^ 4 } }

/-- The refined witness of `toyB` with the gradient bound understated. -/
def toyBLowDh : RefinedBWit :=
  { toyRefinedBWit with R := { toyRefinedBWit.R with dh := 199 / 100 } }

/-- An ordinary route-B certificate passes. -/
theorem toyB_refinedBE_passes :
    checkTorusCertificateV2 routeBRefinedE toyB toyRefinedBWit = true := by decide +kernel

/-- The witness between the thresholds passes with `y₀ = dh s_N`. -/
theorem toyB_refinedBE_gain_passes :
    checkTorusCertificateV2 routeBRefinedE toyB toyBGain = true := by decide +kernel

/-- It fails with `y₀ = M s_N`, in the numerical test. -/
theorem toyB_core_gain_rejects : refinedBCore 2 toyB.params toyB.freqBox toyBGain = false := by
  decide +kernel

/-- So the landed engine rejects it. -/
theorem toyB_refinedB_gain_rejects :
    checkTorusCertificateV2 routeBRefined toyB toyBGain = false := by decide +kernel

/-- And so does the engine without the torsion majorant. -/
theorem toyB_refinedBLN_gain_rejects :
    checkTorusCertificateV2 routeBRefinedLN toyB toyBGain = false := by decide +kernel

/-- An understated gradient bound is rejected. -/
theorem toyB_refinedBE_lowDh_rejects :
    checkTorusCertificateV2 routeBRefinedE toyB toyBLowDh = false := by decide +kernel

/-- `refinedBCoreE` alone accepts that witness. -/
theorem toyB_coreE_lowDh_passes : refinedBCoreE 2 toyB.params toyB.freqBox toyBLowDh = true := by
  decide +kernel

/-- `checkHamClaim` is the check that rejects it. -/
theorem toyB_hamClaim_lowDh_rejects : checkHamClaim toyB toyBLowDh.R = false := by decide +kernel

/-- Inside the combined engine. -/
theorem toyB_routeV2AllE_passes :
    checkTorusCertificateV2 routeV2AllE toyB (Sum.inr toyBGain) = true := by decide +kernel

/-- **The toy torus through `routeBRefinedE`**, at a witness the landed engine rejects. -/
theorem toyB_refinedBE_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_routeBRefinedE_sound toyB_refinedBE_gain_passes toyB_freq toyB_dio

/-- **The toy torus through `routeV2AllE`**. -/
theorem toyB_routeV2AllE_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeV2AllE toyB_routeV2AllE_passes toyB_freq toyB_dio

end KAM.CertificateSharp.V2

end
