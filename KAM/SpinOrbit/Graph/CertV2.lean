/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Cert
public import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# The barrier from a passing v2 certificate

The v2 certifier `KAM.CertificateSharp.V2.checkTorusCertificateV2 E` (any engine `E` with its
witness) runs the landed sub-checks and then the engine's test; `checkTorusCertificateV2_sound`
gives the landed `CertifiedTorus`. So the rotated-frame barrier `soRotBarrier_of_certV2` is
`soRotBarrier_of_certified` fed by the v2 black box, as `soRotBarrier_of_certSharp` is for the
sharp certifier.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

variable {α : Type} [CertArith α]

/-- The static check is the first conjunct of `checkTorusCertificateV2`. -/
theorem checkStatic_of_checkTorusCertificateV2 {E : EngineV2} {c : TorusCertificate 2 α}
    {w : E.Wit} (hc : checkTorusCertificateV2 E c w = true) : checkStatic c = true := by
  simp only [checkTorusCertificateV2, checkV2With, landedBase, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.1.1

/-- **The barrier from a passing ROTATED-frame v2 certificate**: the v2 black box
(`checkTorusCertificateV2_sound`), then `soRotBarrier_of_certified`. Same conclusion as
`soRotBarrier_of_certSharp`; the band is widened by `disp`. -/
theorem soRotBarrier_of_certV2 [LawfulCertArith α] (E : EngineV2) (g : SoGraphCert α) {c : ℚ}
    (hc0 : 0 < c) (hham : g.base.ham = soRotHamExprScaled c) {w : E.Wit}
    (hc : checkTorusCertificateV2 E g.base w = true) (hg : checkSoGraph g = true)
    {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  soRotBarrier_of_certified g hc0 hham (checkStatic_of_checkTorusCertificateV2 hc) hg
    (checkTorusCertificateV2_sound E hc hω hdio) hdio

end KAM.SpinOrbit
