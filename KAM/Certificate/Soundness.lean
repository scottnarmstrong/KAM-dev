/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Gram
public import KAM.Certificate.Sound.Invariance
public import KAM.Certificate.Sound.Energy
public import KAM.Certificate.Sound.Torsion
public import KAM.Certificate.Sound.Smallness
public import KAM.Iso.Apost.G1

/-!
# Soundness of the torus certificate (the black box)

`checkTorusCertificate_hyps` assembles every field of `G1Hyps` from the eight sub-check
contracts (`Sound/*`), and `checkTorusCertificate_sound` feeds them, with the given
Diophantine premise, to the sealed implementation theorem `KAM.Iso.Apost.g1_explicit`; the
explicit displacement bound `C₂ e / (γ² ρ^{2τ})` is then replaced by `disp`.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- All hypotheses of `g1_explicit` from a passing check and a frequency in the box. -/
theorem checkTorusCertificate_hyps {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) : G1Hyps c ωstar := by
  simp only [checkTorusCertificate, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩, hsm⟩ := h
  have S := checkStatic_sound hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq hs hω
  have hH := checkHamBounds_sound hs hh
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  obtain ⟨hball, hDK⟩ := checkEmbedding_sound hs he
  obtain ⟨hTu, hTb⟩ := checkTorsion_sound hs hh he hg ht hω
  obtain ⟨hC1, hdisp⟩ := checkSmallness_sound hs hsm
  exact
    { hn := S.hn, hτ := S.hτ, hρinf := S.hρinf, hρinfρ := S.hρinfρ, hM := S.hM, hσK := S.hσK
      hσB := S.hσB, hσT := S.hσT, hμ := S.hμ, hγbar := S.hγbar, hσω := S.hσω, hν := S.hν
      hωstar := hω0, hopen := hopen, htransl := htransl, hholo := hholo, hper := hper
      hreal := hreal, hbd := hH.2, hK := hK, hKp := hKp, hKr := hKr, hball := hball
      hDK := hDK, hG := checkGram_sound hs hg, hTu := hTu, hTb := hTb, hs1 := S.hs1
      hsσ := S.hsσ, hν1 := hν1, hν2 := hν2, hγ := S.hγ, hγγbar := S.hγγbar, he0 := S.he0
      hE := checkInvariance_sound hs hh he hi hω, hEn := checkEnergy_sound hs hh he hen
      hC1 := hC1, hdisp := hdisp }

/-- **The black box.** A passing certificate, an exact reference vector `ωstar` in its box, and a
proved Diophantine input yield an exact analytic invariant torus `K_∞` within `disp` of `K`,
through the sealed `KAM.Iso.Apost.g1_explicit` instantiated at
`(n, τ, ρ, ρ∞, M, σK, σB, σT, μ, γbar, σω, ν, ω*) := (n, c.tau, c.rho, c.rhoInf, c.M, c.σK, c.σB,
c.σT, c.μ, c.γbar, c.σω, c.nuRay, ωstar)` and applied to
`(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.s, c.γ, c.err, c.E0)`. -/
theorem checkTorusCertificate_sound {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar := by
  have G := checkTorusCertificate_hyps h hω
  obtain ⟨-, -, -, hbody⟩ := KAM.Iso.Apost.g1_explicit G.hn G.hτ G.hρinf G.hρinfρ G.hM G.hσK
    G.hσB G.hσT G.hμ G.hγbar G.hσω G.hν ωstar G.hωstar
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody c.D c.H c.K
    c.params.s c.params.γ c.params.err c.params.E0 G.hopen G.htransl G.hholo G.hper G.hreal G.hbd
    G.hK G.hKp G.hKr G.hball G.hDK G.hG G.hTu G.hTb G.hs1 G.hsσ G.hν1 G.hν2 G.hγ G.hγγbar hdio
    G.he0 G.hE G.hEn G.hC1
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun θ hθ => (h10 θ hθ).trans G.hdisp,
    h11.trans G.hdisp⟩

end KAM.Certificate
