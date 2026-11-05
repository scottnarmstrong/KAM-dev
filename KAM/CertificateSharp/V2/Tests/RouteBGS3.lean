/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteBGS
public import KAM.CertificateSharp.V2.Tests.Fiber3ToyB

/-!
# Route B with three-frequency fibred sites, without the torsion majorant, on `toyB3`

`toyB3` is T3 (frequency `(∛2/2, ∛4/2, 1/2)`, `τ = 2`) on the strip `ρ = 1`
(`Tests/Fiber3ToyB.lean`). Its witness `b3Wit` has six fibred sites, each decided there on its own.
This module reuses those site theorems (`b3_sitesOk`, generic in the run) and decides only the new
parts:

* `routeBRefinedGSLN` (general sites, no torsion majorant, `y₀ = M s_N`): the core is
  `refinedBCoreG`'s (`refinedBCoreGS_ofG`), so only `checkFrameLN` is new;
* `routeBRefinedGSE` (general sites, no torsion majorant, `y₀ = dh s_N`): the run's own numbers at
  `y₀ = dh s_N` (`dh = 4`), with the same fibred sites.

Both give the torus `CertifiedTorus toyB3 cubicFreq`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp

/-- The fibred witness of `toyB3` on the certificate's box, unreflected. -/
def b3WitGS (Xs : ℚ) : RefinedBWitGS := ⟨b3Wit Xs, false, toyB3.freqBox⟩

theorem toyB3_frameLN :
    checkFrameLN toyB3 t3RefClaim.bL t3RefClaim.bN t3RefClaim.bNt = true := by decide +kernel

/-- **`toyB3` through route B with fibred sites, without the torsion majorant.** -/
theorem toyB3_refinedBGSLN_passes :
    checkTorusCertificateV2 routeBRefinedGSLN toyB3 (b3WitGS (1 / 10 ^ 20)) = true :=
  checkTorusCertificateV2_routeBRefinedGSLN_of toyB3_base toyB3_hamClaim toyB3_frameLN
    ((refinedBCoreGS_ofG _ _ _).trans toyB3_core)

theorem toyB3_γ : toyB3.params.γ = 1 / 12 := by decide +kernel

/-- The core at `y₀ = dh s_N`, from its parts; the six sites are those of
`Tests/Fiber3ToyB.lean`. -/
theorem toyB3_coreGSE :
    refinedBCoreGS 3 toyB3.params toyB3.freqBox t3RefClaim.dh (b3WitGS (1 / 10 ^ 20)) = true := by
  refine refinedBCoreGS_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (coverOk_self _ _) ?_ (by decide +kernel)
    (by decide +kernel)
  rw [toyB3_γ]
  exact b3_sitesOk _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl rfl rfl

/-- **`toyB3` through route B with fibred sites and the gradient bound in the energy row.** -/
theorem toyB3_refinedBGSE_passes :
    checkTorusCertificateV2 routeBRefinedGSE toyB3 (b3WitGS (1 / 10 ^ 20)) = true :=
  checkTorusCertificateV2_routeBRefinedGSE_of toyB3_base toyB3_hamClaim toyB3_frameLN
    toyB3_coreGSE

theorem toyB3_dio : IsDiophantine ((toyB3.params.γ : ℚ) : ℝ) ((toyB3.params.tau : ℕ) : ℝ)
    cubicFreq := by
  have h : ((toyB3.params.γ : ℚ) : ℝ) = 1 / 12 := by rw [toyB3_γ]; norm_num
  have ht : ((toyB3.params.tau : ℕ) : ℝ) = 2 := by
    rw [show toyB3.params.tau = 2 by decide +kernel]; norm_num
  rw [h, ht]
  exact cubicFreq_isDiophantine_twelfth

/-- **The toy 3-torus through route B with fibred sites, without the torsion majorant.** -/
theorem toyB3_refinedBGSLN_torus : CertifiedTorus toyB3 cubicFreq :=
  checkTorusCertificateV2_routeBRefinedGSLN_sound toyB3_refinedBGSLN_passes toyCert3_freq toyB3_dio

/-- **The toy 3-torus through route B with fibred sites and the energy row.** -/
theorem toyB3_refinedBGSE_torus : CertifiedTorus toyB3 cubicFreq :=
  checkTorusCertificateV2_routeBRefinedGSE_sound toyB3_refinedBGSE_passes toyCert3_freq toyB3_dio

end KAM.CertificateSharp.V2

end
