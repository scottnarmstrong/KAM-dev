/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Sound

/-!
# The v2 engine interface

The landed `AposterioriEngine` asks for the body `IG1Body` at **every** `ωstar ≠ 0`, so an engine
cannot use the frequency box. Route A of the v2 theorem needs `‖ωstar‖` (through `Θ`) and, with
frequency-specific constants, the frequency itself. `EngineV2` is the interface for such theorems.

* `BaseFacts c ωstar`: what the sub-checks other than the threshold test establish: every
  hypothesis of the a-posteriori theorem at the data of `c`, except the smallness.
* `EngineV2`: a computable test with a witness `Wit` and its soundness, required only for `ωstar`
  in the box, Diophantine, under `BaseFacts`. `sound` is proved for each instance; it is never a
  premise of `checkTorusCertificateV2_sound`.
* `BaseChecker`: a choice of the sub-checks with the proof that they give `BaseFacts`; `landedBase`
  is the landed one, the corner and cosh variants are in `V2/BaseCorner.lean`, `V2/BaseTrig.lean`.
* `checkTorusCertificateV2 E c w`: the landed sub-checks, then `E.test c w`, with soundness
  `checkTorusCertificateV2_sound` concluding the landed `CertifiedTorus c ωstar`.
* `EngineV2.ofEngine`, `sharpV2`: every landed engine is an instance, and at `sharpV2`
  the certifier is `checkTorusCertificateSharp` (`rfl`).
* `EngineV2.orElse`: the minimum over two routes, the witness choosing the route.
* `certifiedTorus_of_ray`: the wiring from `IG1Body`, at a ray bound `σh ≥ σω`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The contract of the sub-checks other than the threshold test, at the data of `c` and `ωstar`:
the hypotheses of `IG1Body` that do not concern smallness. -/
structure BaseFacts (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop where
  hs : checkStatic c = true
  hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
    ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M
  hEm : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
    ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ
  hG : ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det ∧
    ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ
  hTu : IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det
  hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
    (c.params.σT : ℝ) - c.params.μ
  hE : ∀ θ ∈ complexStrip n c.params.rho,
    ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err
  hEn : ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err

omit [CertArith α] in
/-- `C₁ e/(γ⁴ρ^{4τ}) < 1` and `max {C₂, C₃} e/(γ²ρ^{2τ}) ≤ disp` at the parameters. -/
def Admissible (p : CertParams) (C₁ C₂ C₃ : ℝ) : Prop :=
  C₁ * p.err / ((p.γ : ℝ) ^ 4 * (p.rho : ℝ) ^ (4 * (p.tau : ℝ))) < 1 ∧
    max C₂ C₃ * p.err / ((p.γ : ℝ) ^ 2 * (p.rho : ℝ) ^ (2 * (p.tau : ℝ))) ≤ p.disp

/-- A threshold test with a witness, and the soundness of the a-posteriori theorem it encodes,
for the frequencies of the certificate's box. -/
structure EngineV2 where
  /-- The numerical witness of the test (`X⋆`, the schedule, the claimed bounds). -/
  Wit : Type
  /-- The computable test: it reads the certificate and the witness. -/
  test : {n : ℕ} → {α : Type} → [CertArith α] → TorusCertificate n α → Wit → Bool
  /-- A passing test gives the certified torus at every Diophantine frequency of the box. -/
  sound : ∀ {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α] (c : TorusCertificate n α)
    (w : Wit) {ωstar : Fin n → ℝ}, FreqEncloses n c.freqBox ωstar →
    IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar → BaseFacts c ωstar →
    test c w = true → CertifiedTorus c ωstar

/-- A choice of the sub-checks other than the threshold test. -/
structure BaseChecker where
  /-- The conjunction of the sub-checks. -/
  check : {n : ℕ} → {α : Type} → [CertArith α] → TorusCertificate n α → Bool
  /-- They establish `BaseFacts` at every frequency of the box. -/
  sound : ∀ {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α] {c : TorusCertificate n α},
    check c = true → ∀ {ωstar : Fin n → ℝ}, FreqEncloses n c.freqBox ωstar → BaseFacts c ωstar

/-- The certifier of a base checker and an engine. -/
def checkV2With (B : BaseChecker) (E : EngineV2) (c : TorusCertificate n α) (w : E.Wit) : Bool :=
  B.check c && E.test c w

/-- **Soundness of the certifier of a base checker and an engine.** -/
theorem checkV2With_sound [LawfulCertArith α] (B : BaseChecker) (E : EngineV2)
    {c : TorusCertificate n α} {w : E.Wit} (h : checkV2With B E c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar := by
  simp only [checkV2With, Bool.and_eq_true] at h
  exact E.sound c w hω hdio (B.sound h.1 hω) h.2

/-- The landed sub-checks. -/
def landedBase : BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c &&
    checkEnergy c && checkGram c && checkTorsion c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hi⟩, hen⟩, hg⟩, ht⟩ := h
    obtain ⟨hTu, hTb⟩ := checkTorsion_sound hs hh he hg ht hω
    exact ⟨hs, checkHamBounds_sound hs hh, checkEmbedding_sound hs he, checkGram_sound hs hg, hTu,
      hTb, checkInvariance_sound hs hh he hi hω, checkEnergy_sound hs hh he hen⟩

/-- The certifier: every sub-check of `checkTorusCertificate`, the engine's test in place of
`checkSmallness`. -/
def checkTorusCertificateV2 (E : EngineV2) (c : TorusCertificate n α) (w : E.Wit) : Bool :=
  checkV2With landedBase E c w

/-- **Soundness of the v2 certifier.** A passing certificate, an exact reference vector `ωstar` in
its box and a proved Diophantine premise yield the landed `CertifiedTorus c ωstar`. -/
theorem checkTorusCertificateV2_sound [LawfulCertArith α] (E : EngineV2)
    {c : TorusCertificate n α} {w : E.Wit} (h : checkTorusCertificateV2 E c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound landedBase E h hω hdio

/-- `CertifiedTorus` from `IG1Body` at the certificate's constants and a ray bound `σh ≥ σω`:
the wiring of the landed `checkTorusCertificateWith_sound`. `hray` recovers `sinf < σω` from
`sinf < σh` and the certified displacement. -/
theorem certifiedTorus_of_ray [LawfulCertArith α] {c : TorusCertificate n α}
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    {C₁ C₂ C₃ σh : ℝ} (hσ : (c.params.σω : ℝ) ≤ σh) (hA : Admissible c.params C₁ C₂ C₃)
    (hray : ∀ t : ℝ, t < σh → ‖t • ωstar - (c.params.s : ℝ) • ωstar‖ ≤ c.params.disp →
      t < c.params.σω)
    (hbody : KAM.Iso.Charts.IG1Body n (c.params.tau : ℝ) c.params.rho c.params.rhoInf c.params.M
      c.params.σK c.params.σB c.params.σT c.params.μ c.params.γbar σh c.params.nuRay ωstar
      C₁ C₂ C₃) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  have hν2' : (c.params.nuRay : ℝ) ≤ (σh - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody c.D c.H c.K
    c.params.s c.params.γ c.params.err c.params.E0 hopen htransl hholo hper hreal B.hH.2 hK hKp hKr
    B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 (S.hsσ.trans_le hσ) hν1 hν2' S.hγ S.hγγbar hdio S.he0
    B.hE B.hEn hA.1
  have hd : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ)) := by
    have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
    have := Real.rpow_pos_of_pos hρ0 (2 * (c.params.tau : ℝ))
    have := S.hγ
    positivity
  have hmono : ∀ C : ℝ, C ≤ max C₂ C₃ → C * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp :=
    fun C hC => (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC S.he0) hd.le).trans hA.2
  have h11' := h11.trans (hmono _ (le_max_right _ _))
  exact ⟨Kinf, sinf, h1, hray _ h2 h11', h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans (hmono _ (le_max_left _ _)), h11'⟩

/-- `sinf < σω` from the displacement bound, when `disp` is below the room of the ray. -/
theorem ray_lt_of_disp {ωstar : Fin n → ℝ} {s σ d t : ℝ} (hd : d < (σ - s) * ‖ωstar‖)
    (ht : ‖t • ωstar - s • ωstar‖ ≤ d) : t < σ := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs] at ht
  have h1 : (t - s) * ‖ωstar‖ ≤ |t - s| * ‖ωstar‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  by_contra hc
  have h2 : (σ - s) * ‖ωstar‖ ≤ (t - s) * ‖ωstar‖ :=
    mul_le_mul_of_nonneg_right (by linarith [not_lt.1 hc]) (norm_nonneg _)
  linarith

/-! ### Every landed engine is an instance -/

/-- A landed engine as a v2 engine: no witness, the same test. -/
def EngineV2.ofEngine (E : AposterioriEngine) : EngineV2 where
  Wit := Unit
  test := fun c _ => E.test c
  sound := by
    intro n α _ _ c _ ωstar hω hdio B h
    obtain ⟨C₁, C₂, C₃, hC1, hdisp, hbody⟩ := E.sound c B.hs h
    exact certifiedTorus_of_ray hω hdio B le_rfl ⟨hC1, hdisp⟩ (fun _ h _ => h)
      (hbody ωstar (checkStatic_freq B.hs hω).1)

/-- The landed sharp engine, as a v2 engine. -/
def sharpV2 : EngineV2 := EngineV2.ofEngine sharpEngine

/-- The v2 certifier at a landed engine is the landed certifier of that engine. -/
theorem checkTorusCertificateV2_ofEngine (E : AposterioriEngine) (c : TorusCertificate n α) :
    checkTorusCertificateV2 (EngineV2.ofEngine E) c () = checkTorusCertificateWith E c := rfl

/-- **v2 is never worse than the landed certifier.** At `sharpV2` the v2 certifier is
`checkTorusCertificateSharp`. -/
theorem checkTorusCertificateV2_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 sharpV2 c () = checkTorusCertificateSharp c := rfl

/-! ### The minimum over routes -/

/-- Two routes: the witness chooses the route. -/
def EngineV2.orElse (E₁ E₂ : EngineV2) : EngineV2 where
  Wit := E₁.Wit ⊕ E₂.Wit
  test := fun c w => Sum.elim (E₁.test c) (E₂.test c) w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    cases w with
    | inl w => exact E₁.sound c w hω hdio B h
    | inr w => exact E₂.sound c w hω hdio B h

end KAM.CertificateSharp.V2

end
