/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAllLN
public import KAM.CertificateSharp.V2.Tests.RouteBToy

/-!
# Route B without the torsion majorant, in the kernel, on `toyB`

* an ordinary refined witness passes `routeBRefinedLN`, by itself and inside `routeV2AllLN`;
* `toyBNoT`, the same witness with `bT = 0`, passes `routeBRefinedLN` and is rejected by
  `routeBRefined`, whose torsion check is the only one that reads `bT`;
* each of `bL`, `bN`, `bNt` understated is rejected, although `refinedBCore` alone accepts it: the
  frame check is what rejects;
* an understated claim on `H` is rejected;
* the toy torus through both engines, at `toyBNoT`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The refined witness of `toyB`, with the unused torsion majorant set to `0`. -/
def toyBNoT : RefinedBWit := { toyRefinedBWit with R := { toyRefinedBWit.R with bT := 0 } }

/-- The refined witness of `toyB` with `|Lᵀ|` understated. `fitsOk` bounds the stage-0 weights from
below through `bL`, so they are raised with it: the mutant differs only where `refinedBCore` allows. -/
def toyBLowL : RefinedBWit :=
  { toyRefinedBWit with
    core := { toyRefinedBWit.core with
      lam0 := 405 / 100000, lamW0 := 401 / 100000, ePer0 := 401 / 100000 }
    R := { toyRefinedBWit.R with bL := 99 / 100 } }

/-- The refined witness of `toyB` with `|N|` understated. -/
def toyBLowN : RefinedBWit := { toyRefinedBWit with R := { toyRefinedBWit.R with bN := 99 / 100 } }

/-- The refined witness of `toyB` with `|Nᵀ|` understated. -/
def toyBLowNt : RefinedBWit :=
  { toyRefinedBWit with R := { toyRefinedBWit.R with bNt := 99 / 100 } }

/-- An ordinary route-B certificate passes. -/
theorem toyB_refinedBLN_passes :
    checkTorusCertificateV2 routeBRefinedLN toyB toyRefinedBWit = true := by decide +kernel

/-- Changing only `bT`: the new engine accepts. -/
theorem toyB_refinedBLN_noT_passes :
    checkTorusCertificateV2 routeBRefinedLN toyB toyBNoT = true := by decide +kernel

/-- Changing only `bT`: the unchanged engine rejects, in its torsion check. -/
theorem toyB_refinedB_noT_rejects :
    checkTorusCertificateV2 routeBRefined toyB toyBNoT = false := by decide +kernel

theorem toyB_refinedBLN_lowL_rejects :
    checkTorusCertificateV2 routeBRefinedLN toyB toyBLowL = false := by decide +kernel

theorem toyB_refinedBLN_lowN_rejects :
    checkTorusCertificateV2 routeBRefinedLN toyB toyBLowN = false := by decide +kernel

theorem toyB_refinedBLN_lowNt_rejects :
    checkTorusCertificateV2 routeBRefinedLN toyB toyBLowNt = false := by decide +kernel

theorem toyB_core_lowL_passes : refinedBCore 2 toyB.params toyB.freqBox toyBLowL = true := by
  decide +kernel

theorem toyB_core_lowN_passes : refinedBCore 2 toyB.params toyB.freqBox toyBLowN = true := by
  decide +kernel

theorem toyB_core_lowNt_passes : refinedBCore 2 toyB.params toyB.freqBox toyBLowNt = true := by
  decide +kernel

/-- An understated claim on `H` is rejected. -/
theorem toyB_refinedBLN_lowDx_rejects : checkTorusCertificateV2 routeBRefinedLN toyB
    { toyRefinedBWit with R := { toyRefinedBWit.R with dx := 99 / 100 } } = false := by
  decide +kernel

/-- Inside the combined engine. -/
theorem toyB_routeV2AllLN_passes :
    checkTorusCertificateV2 routeV2AllLN toyB (Sum.inr toyBNoT) = true := by decide +kernel

/-- **The toy torus through `routeBRefinedLN`**, with no torsion majorant. -/
theorem toyB_refinedBLN_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_routeBRefinedLN_sound toyB_refinedBLN_noT_passes toyB_freq toyB_dio

/-- **The toy torus through `routeV2AllLN`**. -/
theorem toyB_routeV2AllLN_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeV2AllLN toyB_routeV2AllLN_passes toyB_freq toyB_dio

end KAM.CertificateSharp.V2

end
