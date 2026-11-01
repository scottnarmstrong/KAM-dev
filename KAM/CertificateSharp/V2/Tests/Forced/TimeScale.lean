/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyRouteA
public import KAM.CertificateSharp.V2.Tests.Forced.TinyC2RouteA
public import KAM.SpinOrbit.Rotated

/-!
# Two time normalizations of the forced toy, through their checked transformation

`TinyC2` is `Tiny` with the Hamiltonian doubled (`c = 2`) and the reference vector doubled
(`κ = c/s`): the producer emits the same torus (`timeScale_emb`), and both certificates pass the
whole v2 certifier independently (`Tiny.refinedA_passes`, `TinyC2.refinedA_passes`). The two
normalizations are related by the proved time-scaling identity `invarianceError_const_mul`:
`timeScale_invariance` is the invariance error of `TinyC2` as twice that of `Tiny` at half the
frequency, and `timeScale_ωstar` the doubled reference vector, so the checked residual claims
(`8.2·10⁻¹²` against `4.1·10⁻¹²`) are the identity's factor 2. A drift of the normalization (the
Hamiltonian doubled without the box) is rejected (`Tiny.mut_timeScale`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM KAM.Certificate KAM.SpinOrbit

/-- The two normalizations carry the same torus. -/
theorem timeScale_emb : TinyC2.cert.emb = Tiny.cert.emb := rfl

/-- The Hamiltonian of `TinyC2` is twice that of `Tiny`. -/
theorem timeScale_H : TinyC2.cert.H = fun z => ((2 : ℝ) : ℂ) * Tiny.cert.H z := by
  funext z
  simp only [TorusCertificate.H, TinyC2.cert, Tiny.cert, TinyC2.ham, Tiny.ham, HamExpr.eval]
  push_cast
  ring

/-- The reference vector of `TinyC2` is twice that of `Tiny`. -/
theorem timeScale_ωstar : TinyC2.ωstar = (2 : ℝ) • Tiny.ωstar := by
  have h : (TinyC2.κ : ℝ) = 2 * Tiny.κ := by
    rw [TinyC2.κ, Tiny.κ]; norm_num
  funext i
  fin_cases i
  · simp [TinyC2.ωstar, Tiny.ωstar, lunarRotFreq, h]
    ring
  · simp [TinyC2.ωstar, Tiny.ωstar, lunarRotFreq, h]

/-- **The checked transformation**: the invariance error of `TinyC2` is twice that of `Tiny` at
half the frequency (`invarianceError_const_mul`). -/
theorem timeScale_invariance (ω : Fin 2 → ℝ) (θ : Fin 2 → ℂ) :
    invarianceError TinyC2.cert.H TinyC2.cert.K ω θ =
      ((2 : ℝ) : ℂ) • invarianceError Tiny.cert.H Tiny.cert.K ((2 : ℝ)⁻¹ • ω) θ := by
  have hK : TinyC2.cert.K = Tiny.cert.K := by
    simp only [TorusCertificate.K, timeScale_emb]
  rw [timeScale_H, hK]
  exact invarianceError_const_mul (by norm_num) _ _ _ _

/-- Both normalizations are certified: the tori of `Tiny` at `ω*` and of `TinyC2` at `2 ω*`. -/
theorem timeScale_tori : CertifiedTorus Tiny.cert Tiny.ωstar ∧
    CertifiedTorus TinyC2.cert ((2 : ℝ) • Tiny.ωstar) :=
  ⟨Tiny.refinedA_torus, timeScale_ωstar ▸ TinyC2.refinedA_torus⟩

end KAM.CertificateSharp.V2.Forced

end
