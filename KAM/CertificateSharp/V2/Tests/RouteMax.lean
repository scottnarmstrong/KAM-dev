/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteMax
public import KAM.CertificateSharp.V2.Tests.RouteAll
public import KAM.CertificateSharp.V2.Tests.Fiber3ToyB
public import KAM.CertificateSharp.Hybrid.Tests.T2
public import KAM.CertificateSharp.V2.Tests.RouteBGS
public import KAM.CertificateSharp.V2.Tests.RouteBGS3

/-!
# Every branch of `routeMax` is reachable

For each constructor of `RouteMaxWit` but `.aPacked` (`Tests/RouteMaxPacked.lean`), a toy
certificate passes the whole v2 certifier at `routeMax` on that branch. Each theorem is the branch
equation of `V2/RouteMax.lean` (`rfl`) followed by the toy's own passing theorem of the engine,
so nothing is recomputed here:

| Branch | Toy | Passing theorem reused |
|---|---|---|
| `.sharp` | `toyCert2` | `toyCert2_sharpV2_passes` |
| `.aFrozen` | `toyCert2` | `toyCert2_v2_passes` |
| `.aRefined` | `toyCert2` | `toyCert2_refined_passes` |
| `.aRefinedR` | `toyCert2` | `toyCert2_refinedR_passes` |
| `.aL1` | `toyCert2` | `L1.toyCert2_l1_passes` |
| `.bFrozen` | `toyB` | `toyB_frozenB_passes` |
| `.bRefined` | `toyB` | `toyB_refinedB_passes` |
| `.bLN` | `toyB` | `toyB_refinedBLN_passes` |
| `.bE` | `toyB` | `toyB_refinedBE_gain_passes` (a witness `.bRefined`, `.bLN` reject) |
| `.aG` | `toyCert3` (three frequencies) | `toyCert3_refinedG_passes` |
| `.bG` | `toyB3` (three frequencies) | `toyB3_refinedBG_passes` |
| `.aS` | `toyNeg` (negative clock) | `toyNeg_refinedS_passes` |
| `.hybrid` | `toyCert2H` | `Hybrid.toyHyb_passes` |
| `.bGSLN` | `toyBNeg` (negative clock), `toyB3` | `toyBNeg_refinedBGSLN_passes`, `toyB3_…` |
| `.bGSE` | `toyBNeg`, `toyB3` | `toyBNeg_refinedBGSE_passes`, `toyB3_refinedBGSE_passes` |

A witness of an older combined engine runs unchanged after `RouteMaxWit.of…`
(`toyB_routeMax_ofV2AllE_passes`), and the soundness theorem of `routeMax` gives the tori
(`toyBNeg_routeMax_torus`, `toyB3_routeMax_torus`). The base selection is exercised at the corner
bounds (`toyCert2_routeMax_corner_passes`, `cornerBase.check` decided here).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp

theorem toyCert2_routeMax_sharp : checkTorusCertificateV2 routeMax toyCert2 .sharp = true :=
  (checkV2With_routeMax_sharp landedBase toyCert2).trans toyCert2_sharpV2_passes

theorem toyCert2_routeMax_aFrozen :
    checkTorusCertificateV2 routeMax toyCert2 (.aFrozen toyFrozenWit) = true :=
  (checkV2With_routeMax_aFrozen landedBase toyCert2 _).trans toyCert2_v2_passes

theorem toyCert2_routeMax_aRefined :
    checkTorusCertificateV2 routeMax toyCert2 (.aRefined toyRefinedWit) = true :=
  (checkV2With_routeMax_aRefined landedBase toyCert2 _).trans toyCert2_refined_passes

theorem toyCert2_routeMax_aRefinedR :
    checkTorusCertificateV2 routeMax toyCert2 (.aRefinedR toyRefinedWitR) = true :=
  (checkV2With_routeMax_aRefinedR landedBase toyCert2 _).trans toyCert2_refinedR_passes

theorem toyCert2_routeMax_aL1 :
    checkTorusCertificateV2 routeMax toyCert2 (.aL1 L1.toyL1Wit) = true :=
  (checkV2With_routeMax_aL1 landedBase toyCert2 _).trans L1.toyCert2_l1_passes

theorem toyB_routeMax_bFrozen :
    checkTorusCertificateV2 routeMax toyB (.bFrozen toyFrozenBWit) = true :=
  (checkV2With_routeMax_bFrozen landedBase toyB _).trans toyB_frozenB_passes

theorem toyB_routeMax_bRefined :
    checkTorusCertificateV2 routeMax toyB (.bRefined toyRefinedBWit) = true :=
  (checkV2With_routeMax_bRefined landedBase toyB _).trans toyB_refinedB_passes

theorem toyB_routeMax_bLN : checkTorusCertificateV2 routeMax toyB (.bLN toyRefinedBWit) = true :=
  (checkV2With_routeMax_bLN landedBase toyB _).trans toyB_refinedBLN_passes

/-- The energy-row branch at a witness the branches `.bRefined` and `.bLN` reject. -/
theorem toyB_routeMax_bE : checkTorusCertificateV2 routeMax toyB (.bE toyBGain) = true :=
  (checkV2With_routeMax_bE landedBase toyB _).trans toyB_refinedBE_gain_passes

theorem toyB_routeMax_bLN_gain_rejects :
    checkTorusCertificateV2 routeMax toyB (.bLN toyBGain) = false :=
  (checkV2With_routeMax_bLN landedBase toyB _).trans toyB_refinedBLN_gain_rejects

theorem toyCert3_routeMax_aG :
    checkTorusCertificateV2 routeMax toyCert3 (.aG (t3WitG (1 / 10 ^ 30))) = true :=
  (checkV2With_routeMax_aG landedBase toyCert3 _).trans toyCert3_refinedG_passes

theorem toyB3_routeMax_bG :
    checkTorusCertificateV2 routeMax toyB3 (.bG (b3Wit (1 / 10 ^ 20))) = true :=
  (checkV2With_routeMax_bG landedBase toyB3 _).trans toyB3_refinedBG_passes

theorem toyNeg_routeMax_aS : checkTorusCertificateV2 routeMax toyNeg (.aS toyNegWit) = true :=
  (checkV2With_routeMax_aS landedBase toyNeg _).trans toyNeg_refinedS_passes

theorem toyCert2H_routeMax_hybrid :
    checkTorusCertificateV2 routeMax Hybrid.toyCert2H (.hybrid Hybrid.toyHybWit) = true :=
  (checkV2With_routeMax_hybrid landedBase Hybrid.toyCert2H _).trans Hybrid.toyHyb_passes

theorem toyBNeg_routeMax_bGSLN :
    checkTorusCertificateV2 routeMax toyBNeg (.bGSLN toyBNegWit) = true :=
  (checkV2With_routeMax_bGSLN landedBase toyBNeg _).trans toyBNeg_refinedBGSLN_passes

theorem toyBNeg_routeMax_bGSE :
    checkTorusCertificateV2 routeMax toyBNeg (.bGSE toyBNegWit) = true :=
  (checkV2With_routeMax_bGSE landedBase toyBNeg _).trans toyBNeg_refinedBGSE_passes

theorem toyB3_routeMax_bGSLN :
    checkTorusCertificateV2 routeMax toyB3 (.bGSLN (b3WitGS (1 / 10 ^ 20))) = true :=
  (checkV2With_routeMax_bGSLN landedBase toyB3 _).trans toyB3_refinedBGSLN_passes

theorem toyB3_routeMax_bGSE :
    checkTorusCertificateV2 routeMax toyB3 (.bGSE (b3WitGS (1 / 10 ^ 20))) = true :=
  (checkV2With_routeMax_bGSE landedBase toyB3 _).trans toyB3_refinedBGSE_passes

/-- A witness of `routeV2AllE` runs unchanged. -/
theorem toyB_routeMax_ofV2AllE_passes :
    checkTorusCertificateV2 routeMax toyB (.ofV2AllE (Sum.inr toyBGain)) = true :=
  (checkV2With_routeMax_ofV2AllE landedBase toyB _).trans toyB_routeV2AllE_passes

/-- **The negative-clock torus through `routeMax`.** -/
theorem toyBNeg_routeMax_torus : CertifiedTorus toyBNeg (-![lunarNuMinus / 2, 1 / 2]) :=
  checkTorusCertificateV2_routeMax_sound toyBNeg_routeMax_bGSE (freqEncloses_negBox toyCert2_freq)
    toyBNeg_dio

/-- **The three-frequency torus through `routeMax`.** -/
theorem toyB3_routeMax_torus : CertifiedTorus toyB3 cubicFreq :=
  checkTorusCertificateV2_routeMax_sound toyB3_routeMax_bGSE toyCert3_freq toyB3_dio

/-! ### The base selection -/

theorem toyCert2_cornerBase : cornerBase.check toyCert2 = true := by decide +kernel

/-- The corner base and route A refined. -/
theorem toyCert2_routeMax_corner_passes :
    checkTorusCertificateMax toyCert2 .corner (.aRefined toyRefinedWit) = true := by
  have h := toyCert2_refined_passes
  simp only [checkTorusCertificateV2, checkV2With, Bool.and_eq_true] at h
  simp only [checkTorusCertificateMax_eq, BaseSel.toBase, Bool.and_eq_true]
  exact ⟨toyCert2_cornerBase, h.2⟩

end KAM.CertificateSharp.V2

end
