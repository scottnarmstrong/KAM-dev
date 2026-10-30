/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Graph.Cert
public import KAM.CertificateSharp.Sound

/-!
# The barrier from a passing sharp certificate

The sharp certifier `KAM.CertificateSharp.checkTorusCertificateSharp` (D36) runs the same
sub-checks as `checkTorusCertificate` with the sharp smallness test, and
`checkTorusCertificateSharp_sound` gives the same `CertifiedTorus`. So the rotated-frame barrier
`soRotBarrier_of_certSharp` is `soRotBarrier_of_certified` (shared with `soRotBarrier_of_cert`)
fed by the sharp black box.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate KAM.CertificateSharp

variable {α : Type} [CertArith α]

/-- The static check is the first conjunct of `checkTorusCertificateSharp`. -/
theorem checkStatic_of_checkTorusCertificateSharp {c : TorusCertificate 2 α}
    (hc : checkTorusCertificateSharp c = true) : checkStatic c = true := by
  simp only [checkTorusCertificateSharp, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.1.1

/-- **The barrier from a passing ROTATED-frame sharp certificate**: the sharp black box
(`checkTorusCertificateSharp_sound`), then `soRotBarrier_of_certified`. Same conclusion as
`soRotBarrier_of_cert`; the band is widened by `disp`. -/
theorem soRotBarrier_of_certSharp [LawfulCertArith α] (g : SoGraphCert α) {c : ℚ} (hc0 : 0 < c)
    (hham : g.base.ham = soRotHamExprScaled c) (hc : checkTorusCertificateSharp g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  soRotBarrier_of_certified g hc0 hham (checkStatic_of_checkTorusCertificateSharp hc) hg
    (checkTorusCertificateSharp_sound hc hω hdio) hdio

end KAM.SpinOrbit
