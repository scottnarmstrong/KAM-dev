/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Sharp

/-!
# The sharp engine

`IsoSharpG1` is the *type* of `KAM.Iso.Sharp.g1_sharp` (package A7: binders of
`KAM.Iso.Apost.g1_explicit`, conclusion with `sharpIsoC1`, `sharpIsoC2`, `sharpIsoC3` at
Rüssmann's data). `sharpEngineOf` is the engine of the sharp threshold test, conditional on a proof
`G : IsoSharpG1`; `checkTorusCertificateSharp_sound_of` is the corresponding conditional soundness
(a helper with a distinct name). The unconditional instance is
`sharpEngineOf KAM.Iso.Sharp.g1_sharp` (a one-line definition once A7 is committed).
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Sharp KAM.Iso.Sharp KAM.Certificate CertArith

/-- The type of `KAM.Iso.Sharp.g1_sharp` (Rüssmann's data `(τ, cohConstR n τ)`). -/
def IsoSharpG1 : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {τ : ℝ}, (n : ℝ) - 1 ≤ τ → ∀ {ρ ρinf : ℝ}, 0 < ρinf → ρinf < ρ →
    ∀ {M σK σB σT μ γbar σω ν : ℝ}, 0 < M → 0 < σK → 0 < σB → 0 < σT → 0 < μ → 0 < γbar →
    1 < σω → 0 < ν → ∀ ωstar : Fin n → ℝ, ωstar ≠ 0 →
    0 < sharpIsoC1 n τ (cohConstR n τ) M σK σB σT γbar μ ν τ ρ ρinf ∧
      0 < sharpIsoC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf ∧
      0 < sharpIsoC3 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf ∧
      KAM.Iso.Charts.IG1Body n τ ρ ρinf M σK σB σT μ γbar σω ν ωstar
        (sharpIsoC1 n τ (cohConstR n τ) M σK σB σT γbar μ ν τ ρ ρinf)
        (sharpIsoC2 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf)
        (sharpIsoC3 n τ (cohConstR n τ) M σK σB σT γbar τ ρ ρinf)

/-- The sharp engine, from the sharp isoenergetic theorem. -/
def sharpEngineOf (G : IsoSharpG1) : AposterioriEngine where
  test := fun c => sharpTest c
  sound := by
    intro n α _ _ c hs h
    have S := checkStatic_sound hs
    obtain ⟨h1, h2⟩ := sharpTest_arith hs h
    exact ⟨_, _, _, h1, h2, fun ωstar hω =>
      (G S.hn S.hτ S.hρinf S.hρinfρ S.hM S.hσK S.hσB S.hσT S.hμ S.hγbar S.hσω S.hν ωstar hω).2.2.2⟩

theorem checkTorusCertificateWith_sharp (G : IsoSharpG1) {n : ℕ} {α : Type} [CertArith α]
    (c : TorusCertificate n α) :
    checkTorusCertificateWith (sharpEngineOf G) c = checkTorusCertificateSharp c := rfl

/-- Soundness of the sharp certifier, conditional on the sharp theorem (`G`); see the module
docstring. -/
theorem checkTorusCertificateSharp_sound_of (G : IsoSharpG1) {n : ℕ} {α : Type} [CertArith α]
    [LawfulCertArith α] {c : TorusCertificate n α} (h : checkTorusCertificateSharp c = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateWith_sound (sharpEngineOf G) h hω hdio

end KAM.CertificateSharp
