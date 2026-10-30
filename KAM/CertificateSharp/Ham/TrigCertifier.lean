/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Engine
public import KAM.CertificateSharp.Ham.SplitBounds

/-!
# The engine certifier with the cosh ball pass

`checkTorusCertificateTrigWith E` is `checkTorusCertificateWith E` with `checkHamBounds` replaced
by `checkHamBoundsTrig`. The new sub-check proves the same `G1Hyps` field (the conclusion of
`checkHamBounds_sound`), so the soundness proof is that of `checkTorusCertificateWith_sound` with
the `_of` forms of the landed lemmas, which take that conclusion as their premise.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

/-- All sub-checks of the engine certifier, with the cosh ball pass for `H`. -/
def checkTorusCertificateTrigWith (E : AposterioriEngine) {n : ℕ} {α : Type} [CertArith α]
    (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBoundsTrig c && checkEmbedding c && checkInvariance c &&
    checkEnergy c && checkGram c && checkTorsion c && E.test c

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness of the engine certifier with the cosh ball pass.** -/
theorem checkTorusCertificateTrigWith_sound (E : AposterioriEngine) {c : TorusCertificate n α}
    (h : checkTorusCertificateTrigWith E c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar := by
  simp only [checkTorusCertificateTrigWith, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩, hsm⟩ := h
  have S := checkStatic_sound hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq hs hω
  have hH := checkHamBoundsTrig_sound hs hh
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  have hE := checkEmbedding_sound hs he
  obtain ⟨hball, hDK⟩ := hE
  obtain ⟨hTu, hTb⟩ := checkTorsion_sound_of hs hH ⟨hball, hDK⟩ ht hω
  obtain ⟨C₁, C₂, C₃, hC1, hdisp, hbody⟩ := E.sound c hs hsm
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody ωstar hω0 c.D c.H c.K
    c.params.s c.params.γ c.params.err c.params.E0 hopen htransl hholo hper hreal hH.2 hK hKp hKr
    hball hDK (checkGram_sound hs hg) hTu hTb S.hs1 S.hsσ hν1 hν2 S.hγ S.hγγbar hdio S.he0
    (checkInvariance_sound_of hs hH ⟨hball, hDK⟩ hi hω)
    (checkEnergy_sound_of hs hH ⟨hball, hDK⟩ hen) hC1
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

end KAM.CertificateSharp

end
