/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefinedRefEngine
public import KAM.CertificateSharp.V2.Tests.Refined

/-!
# Stage 2 with lever L8′ in the kernel, on the toy T2

The witness of `Tests/Refined.lean`, with the two numbers of the lever. `toyCert2_refinedR_passes`
runs the whole certifier by `decide +kernel`, and `toyCert2_refinedR_torus` is the soundness theorem
at the reference frequency, through `Ref.iso_g1_branch_R`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The witness of T2 with lever L8′. -/
def toyRefinedWitR : RefinedWitR where
  base := toyRefinedWit
  bF := 1 / 1000
  bT := 1 / 1000

theorem toyCert2_refinedCoreR :
    refinedCoreR 2 toyCert2.params toyCert2.freqBox toyRefinedWitR = true := by decide +kernel

/-- The whole v2 certifier on T2, with lever L8′. -/
theorem toyCert2_refinedR_passes :
    checkTorusCertificateV2 routeARefinedR toyCert2 toyRefinedWitR = true := by decide +kernel

/-- The same through the combined engine, naming the route. -/
theorem toyCert2_routeAV2'_passes :
    checkTorusCertificateV2 routeAV2' toyCert2 (Sum.inr (Sum.inr toyRefinedWitR)) = true := by
  decide +kernel

/-- **The toy torus through route A with lever L8′.** -/
theorem toyCert2_refinedR_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeARefinedR toyCert2_refinedR_passes toyCert2_freq (by
    have h : ((toyCert2.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

/-- A budget of `𝒯_ab` over `β_T = 1/222` is rejected. -/
theorem toyCert2_refinedCoreR_rejects :
    refinedCoreR 2 toyCert2.params toyCert2.freqBox { toyRefinedWitR with bT := 1 / 100 } = false :=
      by decide +kernel

end KAM.CertificateSharp.V2

end
