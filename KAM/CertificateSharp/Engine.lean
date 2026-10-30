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
public import KAM.Certificate.Soundness

/-!
# The certifier parametric in the a-posteriori theorem

`AposterioriEngine` bundles a computable threshold test on a torus certificate and the soundness
of that test: when it passes (on a certificate whose static data is valid), the a-posteriori
isoenergetic body `KAM.Iso.Charts.IG1Body` holds for some constants `C₁, C₂, C₃` at the
certificate's data, with `C₁ e/(γ⁴ρ^{4τ}) < 1` and `max {C₂, C₃} e/(γ² ρ^{2τ}) ≤ disp`. The field
`sound` is proved for each instance; it is never a premise of `checkTorusCertificateWith_sound`.

`checkTorusCertificateWith E` is `checkTorusCertificate` with `checkSmallness` replaced by
`E.test`, every other sub-check unchanged. The instance `oldEngine` (`checkSmallness`, sealed
`KAM.Iso.Apost.g1_explicit`) is the regression check: `checkTorusCertificateWith oldEngine =
checkTorusCertificate` by `rfl`.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

/-- A threshold test together with the soundness of the a-posteriori theorem it encodes. -/
structure AposterioriEngine where
  /-- The computable test on the certificate's parameters. -/
  test : {n : ℕ} → {α : Type} → [CertArith α] → TorusCertificate n α → Bool
  /-- A passing test on a statically valid certificate yields the body of the a-posteriori
  theorem with an admissible smallness and displacement. -/
  sound : ∀ {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α] (c : TorusCertificate n α),
    checkStatic c = true → test c = true →
    ∃ C₁ C₂ C₃ : ℝ,
      C₁ * c.params.err / ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ)))
        < 1 ∧
      max C₂ C₃ * c.params.err /
        ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤
          c.params.disp ∧
      ∀ ωstar : Fin n → ℝ, ωstar ≠ 0 →
        KAM.Iso.Charts.IG1Body n (c.params.tau : ℝ) c.params.rho c.params.rhoInf c.params.M
          c.params.σK c.params.σB c.params.σT c.params.μ c.params.γbar c.params.σω
          c.params.nuRay ωstar C₁ C₂ C₃

/-- The certifier of an engine: all sub-checks of `checkTorusCertificate`, the engine's test in
place of `checkSmallness`. -/
def checkTorusCertificateWith (E : AposterioriEngine) {n : ℕ} {α : Type} [CertArith α]
    (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c && checkEnergy c &&
    checkGram c && checkTorsion c && E.test c

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness of the engine-parametric certifier.** -/
theorem checkTorusCertificateWith_sound (E : AposterioriEngine) {c : TorusCertificate n α}
    (h : checkTorusCertificateWith E c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar := by
  simp only [checkTorusCertificateWith, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩, hsm⟩ := h
  have S := checkStatic_sound hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq hs hω
  have hH := checkHamBounds_sound hs hh
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  obtain ⟨hball, hDK⟩ := checkEmbedding_sound hs he
  obtain ⟨hTu, hTb⟩ := checkTorsion_sound hs hh he hg ht hω
  obtain ⟨C₁, C₂, C₃, hC1, hdisp, hbody⟩ := E.sound c hs hsm
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody ωstar hω0 c.D c.H c.K
    c.params.s c.params.γ c.params.err c.params.E0 hopen htransl hholo hper hreal hH.2 hK hKp hKr
    hball hDK (checkGram_sound hs hg) hTu hTb S.hs1 S.hsσ hν1 hν2 S.hγ S.hγγbar hdio S.he0
    (checkInvariance_sound hs hh he hi hω) (checkEnergy_sound hs hh he hen) hC1
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

/-! ### Instance (a): the existing theorem -/

/-- The existing theorem `KAM.Iso.Apost.g1_explicit` with the existing `checkSmallness`. -/
def oldEngine : AposterioriEngine where
  test := fun c => checkSmallness c
  sound := by
    intro n α _ _ c hs hsm
    have S := checkStatic_sound hs
    obtain ⟨hC1, hdisp⟩ := checkSmallness_sound hs hsm
    refine ⟨_, _, _, hC1, by rwa [max_self], fun ωstar hω => ?_⟩
    exact (KAM.Iso.Apost.g1_explicit S.hn S.hτ S.hρinf S.hρinfρ S.hM S.hσK S.hσB S.hσT S.hμ
      S.hγbar S.hσω S.hν ωstar hω).2.2.2

omit [LawfulCertArith α] in
/-- Regression: the generic certifier at `oldEngine` is `checkTorusCertificate`. -/
theorem checkTorusCertificateWith_old (c : TorusCertificate n α) :
    checkTorusCertificateWith oldEngine c = checkTorusCertificate c := rfl

/-- Regression: the generic soundness theorem at `oldEngine` reproduces
`checkTorusCertificate_sound`. -/
theorem checkTorusCertificate_sound_via_engine {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateWith_sound oldEngine h hω hdio

end KAM.CertificateSharp
