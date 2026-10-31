/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAll
public import KAM.CertificateSharp.V2.Tests.Frozen
public import KAM.CertificateSharp.V2.Tests.L1Toy
public import KAM.CertificateSharp.V2.Tests.RefinedRef
public import KAM.CertificateSharp.V2.Tests.RouteBToy

/-!
# Every route of `routeV2All` in the kernel, on the toy T2

One `decide +kernel` per route, each running the whole v2 certifier at `routeV2All` with the witness
of the module docstring of `V2/RouteAll.lean`. The witnesses are those of the route's own toy test.

Route B asks `ρ ≤ 1` and T2 has `ρ = 9`, so its two rows run on `toyB`, T2 on the strip `ρ = 1`
(`Tests/RouteBToy.lean`); on T2 itself route B rejects (`toyCert2_routeV2All_bRefined_rejects`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

theorem toyCert2_routeV2All_sharp_passes :
    checkTorusCertificateV2 routeV2All toyCert2 (Sum.inl ()) = true := by decide +kernel

theorem toyCert2_routeV2All_aFrozen_passes : checkTorusCertificateV2 routeV2All toyCert2
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl toyFrozenWit))))) = true := by decide +kernel

theorem toyCert2_routeV2All_aRefined_passes : checkTorusCertificateV2 routeV2All toyCert2
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr toyRefinedWit))))) = true := by decide +kernel

theorem toyCert2_routeV2All_aRefinedR_passes : checkTorusCertificateV2 routeV2All toyCert2
    (Sum.inr (Sum.inl (Sum.inl (Sum.inr toyRefinedWitR)))) = true := by decide +kernel

theorem toyCert2_routeV2All_aL1_passes : checkTorusCertificateV2 routeV2All toyCert2
    (Sum.inr (Sum.inl (Sum.inr L1.toyL1Wit))) = true := by decide +kernel

theorem toyB_routeV2All_bFrozen_passes : checkTorusCertificateV2 routeV2All toyB
    (Sum.inr (Sum.inr (Sum.inl toyFrozenBWit))) = true := by decide +kernel

theorem toyB_routeV2All_bRefined_passes : checkTorusCertificateV2 routeV2All toyB
    (Sum.inr (Sum.inr (Sum.inr toyRefinedBWit))) = true := by decide +kernel

/-- Route B does not reach T2 itself: `ρ = 9`. -/
theorem toyCert2_routeV2All_bRefined_rejects : checkTorusCertificateV2 routeV2All toyCert2
    (Sum.inr (Sum.inr (Sum.inr toyRefinedBWit))) = false := by decide +kernel

/-- **The toy torus through `routeV2All`**, at the witness of the ℓ¹ entry. -/
theorem toyCert2_routeV2All_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeV2All toyCert2_routeV2All_aL1_passes toyCert2_freq (by
    have h : ((toyCert2.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

/-- **The strip torus through `routeV2All`**, at the refined witness of route B. -/
theorem toyB_routeV2All_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeV2All toyB_routeV2All_bRefined_passes toyB_freq toyB_dio

end KAM.CertificateSharp.V2

end
