/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefinedS
public import KAM.CertificateSharp.V2.Tests.Refined

/-!
# Sites with a negative last coordinate, in the kernel, on the toy T2

`toyNeg` is T2 with `H ↦ -H` and `ω* ↦ -ω*` on the same embedding: `X_{-H} = -X_H` and
`∂_{-ω} K = -∂_ω K`, so the torus is the same, its last coordinate is `-1/2`, and the bordered
torsion and its inverse change sign. It is a certificate in its own right, and every sub-check of
the base runs on it.

* the landed `routeARefined` rejects it, in `clockOk`: a last coordinate `-1/2` is not `κ = 1/2 > 0`;
* `routeARefinedS` accepts it, on the reflected box and on a short box containing that box;
* a box that does not contain the certificate's box is rejected, and so is the wrong sign;
* the toy torus at `-(ν₋/2, 1/2)`;
* T2 itself passes at `neg = false` on its own box, as `refinedCoreS_ofRefined` says.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- T2 with the sign of `H` and of the frequency changed. -/
def toyNeg : TorusCertificate 2 ℚ :=
  { toyCert2 with
    ham := .mul (.const (-1)) toyT2Ham
    freqBox := negBox toyCert2.freqBox
    torsInv := toyT2TorsInv.map (List.map fun z => ⟨-z.re, -z.im⟩) }

/-- The reflected box is T2's box. -/
def toyNegWit : RefinedWitS := ⟨toyRefinedWit, true, toyCert2.freqBox⟩

/-- A short box of the reflection: the last coordinate stays exact. -/
def toyShortBox : FreqBox := [(4876902 / 10 ^ 7, 1 / 10 ^ 6), (1 / 2, 0)]

/-- The short box. -/
def toyNegShort : RefinedWitS := ⟨toyRefinedWit, true, toyShortBox⟩

/-- A box that misses the certificate's box. -/
def toyNegMiss : RefinedWitS := ⟨toyRefinedWit, true, [(1 / 2, 1 / 10 ^ 9), (1 / 2, 0)]⟩

/-- The wrong sign: the box of `+ω*`, with a clock that `-1/2` does not fit. -/
def toyNegWrong : RefinedWitS := ⟨toyRefinedWit, false, toyCert2.freqBox⟩

theorem toyNeg_base : landedBase.check toyNeg = true := by decide +kernel

/-- The landed engine rejects the negative clock. -/
theorem toyNeg_refined_rejects :
    checkTorusCertificateV2 routeARefined toyNeg toyRefinedWit = false := by decide +kernel

theorem toyNeg_clock_rejects : clockOk toyNeg.freqBox toyRefinedWit.κ = false := by decide +kernel

/-- The new engine accepts it. -/
theorem toyNeg_refinedS_passes :
    checkTorusCertificateV2 routeARefinedS toyNeg toyNegWit = true := by decide +kernel

theorem toyNeg_short_passes :
    checkTorusCertificateV2 routeARefinedS toyNeg toyNegShort = true := by decide +kernel

theorem toyNeg_miss_rejects :
    checkTorusCertificateV2 routeARefinedS toyNeg toyNegMiss = false := by decide +kernel

theorem toyNeg_wrong_rejects :
    checkTorusCertificateV2 routeARefinedS toyNeg toyNegWrong = false := by decide +kernel

/-- T2 itself, at its own box. -/
theorem toyCert2_refinedS_passes : checkTorusCertificateV2 routeARefinedS toyCert2
    ⟨toyRefinedWit, false, toyCert2.freqBox⟩ = true := by decide +kernel

/-- Inside the combined engine. -/
theorem toyNeg_routeV2AllS_passes :
    checkTorusCertificateV2 routeV2AllS toyNeg (Sum.inr toyNegShort) = true := by decide +kernel

theorem toyNeg_freq : FreqEncloses 2 toyNeg.freqBox (-![lunarNuMinus / 2, 1 / 2]) :=
  freqEncloses_negBox toyCert2_freq

theorem toyNeg_dio : IsDiophantine ((toyNeg.params.γ : ℚ) : ℝ) ((toyNeg.params.tau : ℕ) : ℝ)
    (-![lunarNuMinus / 2, 1 / 2]) := by
  have h : ((toyNeg.params.γ : ℚ) : ℝ) = 1 / 42 := by
    rw [show toyNeg.params.γ = 1 / 42 by decide +kernel]; norm_num
  have ht : ((toyNeg.params.tau : ℕ) : ℝ) = 1 := by
    rw [show toyNeg.params.tau = 1 by decide +kernel]; norm_num
  rw [h, ht]
  exact isDiophantine_neg lunarNuMinus_half_isDiophantine

/-- **The toy torus at the negative frequency**, through `routeARefinedS`. -/
theorem toyNeg_torus : CertifiedTorus toyNeg (-![lunarNuMinus / 2, 1 / 2]) :=
  checkTorusCertificateV2_routeARefinedS_sound toyNeg_short_passes toyNeg_freq toyNeg_dio

end KAM.CertificateSharp.V2

end
