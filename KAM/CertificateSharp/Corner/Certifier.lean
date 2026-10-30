/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Corner.Checks
public import KAM.CertificateSharp.Sound

/-!
# The corner certifier

`checkTorusCertificateCorner E` is `checkTorusCertificateWith E` with `checkEmbedding` and
`checkInvariance` replaced by their corner variants (`Corner/Checks.lean`): the other sub-checks
(static, Hamiltonian bounds, energy, Gram, torsion) are the landed ones, and the threshold test is
the engine's. Its soundness `checkTorusCertificateCorner_sound` has exactly the conclusion of
`checkTorusCertificateWith_sound`; `checkTorusCertificateCornerSharp` is the instance at
`sharpEngine`.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The corner certifier of an engine. -/
def checkTorusCertificateCorner (E : AposterioriEngine) (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbeddingCorner c && checkInvarianceCorner c &&
    checkEnergy c && checkGram c && checkTorsion c && E.test c

variable [LawfulCertArith α]

/-- **Soundness of the corner certifier**, for every engine: the same conclusion as
`checkTorusCertificateWith_sound`. -/
theorem checkTorusCertificateCorner_sound (E : AposterioriEngine) {c : TorusCertificate n α}
    (h : checkTorusCertificateCorner E c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar := by
  simp only [checkTorusCertificateCorner, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩, hsm⟩ := h
  have S := checkStatic_sound hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq hs hω
  have hH := checkHamBounds_sound hs hh
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  have hemb := checkEmbeddingCorner_sound hs he
  obtain ⟨hTu, hTb⟩ := checkTorsion_sound_of hs hH hemb ht hω
  obtain ⟨C₁, C₂, C₃, hC1, hdisp, hbody⟩ := E.sound c hs hsm
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody ωstar hω0 c.D c.H c.K
    c.params.s c.params.γ c.params.err c.params.E0 hopen htransl hholo hper hreal hH.2 hK hKp hKr
    hemb.1 hemb.2 (checkGram_sound hs hg) hTu hTb S.hs1 S.hsσ hν1 hν2 S.hγ S.hγγbar hdio S.he0
    (checkInvarianceCorner_sound_of hs hH hemb hi hω) (checkEnergy_sound_of hs hH hemb hen) hC1
  have hd : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ)) := by
    have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
    have := Real.rpow_pos_of_pos hρ0 (2 * (c.params.tau : ℝ))
    have := S.hγ
    positivity
  have hmono : ∀ C : ℝ, C ≤ max C₂ C₃ → C * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp :=
    fun C hC => (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC S.he0) hd.le).trans
      hdisp
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans (hmono _ (le_max_left _ _)),
    h11.trans (hmono _ (le_max_right _ _))⟩

/-- The corner certifier with the sharp engine. -/
def checkTorusCertificateCornerSharp (c : TorusCertificate n α) : Bool :=
  checkTorusCertificateCorner sharpEngine c

/-- Soundness of the corner certifier with the sharp engine: unconditional. -/
theorem checkTorusCertificateCornerSharp_sound {c : TorusCertificate n α}
    (h : checkTorusCertificateCornerSharp c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateCorner_sound sharpEngine h hω hdio

end KAM.CertificateSharp
