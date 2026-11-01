/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRoutes
public import KAM.Application.Certified

/-!
# Reading `Micro.sharp_torus` in the real coordinates of the model

`sharp_torus : CertifiedTorus cert ωstar` (`MicroRoutes`) is a statement about a complex torus on
a strip. `real_torus` reads it with the application adapters (`KAM/Application/Certified.lean`) in
the real coordinates `(θ, I) ∈ ℝ² × ℝ²` of the forced toy, `θ = (θ₀, θ₁)` with `θ₁` the time and
`I = (p, J)`: there is an analytic real torus `k` of the real Hamiltonian `realHam cert.H` with
`k (θ + m) = k θ + (m, 0)`, whose lines `t ↦ k (θ + t • ω)` solve Hamilton's equations, on the
level `H = E₀`; it lies within `disp` of the certificate's own real torus `realRestriction cert.K`
at every real angle; its frequency is `ω = s∞ • ωstar` with `1 < s∞ < σω`,
`|s∞ - s| ‖ωstar‖ ≤ disp`, and `ω` is `(s∞ γ, τ)`-Diophantine. It is the pattern of
`docs/certifier/QUICKSTART.md` for a tag of one's own, kept in the default build so that the
pattern is checked.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM KAM.Certificate KAM.Application

/-- **The real reading of `sharp_torus`**: a real model torus of the certificate's Hamiltonian,
where it lies (`disp`-close to the certificate's real torus), and its frequency. -/
theorem real_torus : ∃ (k : (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ)) (sinf : ℝ),
    IsRealModelTorus (realHam cert.H) (sinf • ωstar) (cert.params.E0 : ℝ) k ∧
    (∀ θ, ‖k θ - realRestriction cert.K θ‖ ≤ (cert.params.disp : ℝ)) ∧
    1 < sinf ∧ sinf < (cert.params.σω : ℝ) ∧
    |sinf - (cert.params.s : ℝ)| * ‖ωstar‖ ≤ (cert.params.disp : ℝ) ∧
    IsDiophantine (sinf * (cert.params.γ : ℝ)) (cert.params.tau : ℝ) (sinf • ωstar) := by
  obtain ⟨Kinf, sinf, hT⟩ := (certifiedTorus_iff cert ωstar).1 sharp_torus
  exact ⟨realRestriction Kinf, sinf, hT.isRealModelTorus static_ok
    (isRealHolo_of_checkHamBounds static_ok hamBounds_ok), hT.norm_realRestriction_sub_le static_ok,
    hT.1, hT.2.1, hT.abs_sub_mul_norm_le, hT.isDiophantine dio⟩

end KAM.CertificateSharp.V2.Forced.Micro

end
