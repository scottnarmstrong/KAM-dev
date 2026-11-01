/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBEngine
public import KAM.CertificateSharp.Frame.MajorantsLN
import Mathlib.Tactic.Linarith

/-!
# Route B at the refined data, without the torsion majorant

`routeBRefined` calls `checkFrameMajorants`, which builds the torsion models and bounds them by the
claimed `bT`. Route B never reads `bT`: `refinedBCore` and `refHypB_of` use `bL`, `bN`, `bNt` only.
This module adds, next to the unchanged `routeBRefined`, the same route with that check removed:

* `FrameFactsLN`: the part of `FrameFacts` on `K`;
* `refHypB_ofLN`, `refinedBCore_soundLN`: `refHypB_of` and `refinedBCore_sound` at `FrameFactsLN`;
* `refinedBLNTest`, `routeBRefinedLN`: the test and the engine, at the same witness `RefinedBWit`;
* `refinedBLNTest_bT`: the test does not depend on `bT`;
* `checkTorusCertificateV2_routeBRefinedLN_sound`: the certifier at this engine.

The base checks are those of `checkTorusCertificateV2`, in particular `checkTorsion`, the inverse of
the averaged extended torsion: a different obligation, which the branch `iso_g1_branch_B` consumes.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Iso.Sharp2.RouteB KAM.Iso.Apost

variable {n : ℕ} {α : Type} [CertArith α]

/-- The bounds on the frame of `K` that route B reads: `FrameFacts` without the torsion. -/
structure FrameFactsLN (c : TorusCertificate n α) (R : RefClaim) : Prop where
  bL : ∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
    ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤ R.bL
  bN : ∀ θ ∈ complexStrip n c.params.rho, ∀ r : Fin n ⊕ Fin n,
    ∑ j : Fin n, ‖normalMat c.K θ r j‖ ≤ R.bN
  bNt : ∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
    ∑ r : Fin n ⊕ Fin n, ‖normalMat c.K θ r j‖ ≤ R.bNt

/-- `RefHypB` from the claimed bounds, as `refHypB_of`, without any bound on the torsion. -/
theorem refHypB_ofLN {N : NumB n} {c : TorusCertificate n α} {R : RefClaim}
    (hn : 1 ≤ n) (hρ : N.ρ = c.params.rho) (hρ0 : (0 : ℝ) < c.params.rho)
    (hM1 : N.M1 = R.dx) (hM2 : N.M2 = R.d2x) (hcTh : N.cTh = 2 * R.dx)
    (hcDTh : N.cDTh = 2 * R.d2x) (hopen : IsOpen c.D)
    (hdiff : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ c.H)) c.D)
    (hH : HamFacts c R) (hF : FrameFactsLN c R) :
    RefHypB N ⟨R.bL, R.bN, R.bNt⟩ c.D c.H c.K N.ρ := by
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n c.params.rho := fun i => by simpa using hρ0
  have j0 : Fin n := ⟨0, hn⟩
  have hbL : (0 : ℝ) ≤ R.bL :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bL 0 h00 j0)
  have hbN : (0 : ℝ) ≤ R.bN :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bN 0 h00 (Sum.inl j0))
  have hbNt : (0 : ℝ) ≤ R.bNt :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bNt 0 h00 j0)
  have hs : ∀ θ ∈ complexStrip n N.ρ, θ ∈ complexStrip n c.params.rho := fun θ hθ => hρ ▸ hθ
  exact
    { dX := fun z hz => hM1 ▸ hH.dx z hz
      d2X := fun z hz => hM2 ▸ hH.d2x z hz
      comm := fun z hz => hcTh ▸ norm_hamComm_le (hH.dx z hz)
      lip := fun z _ z' _ hseg => hcDTh ▸ norm_hamComm_sub_le_of hopen hdiff hH.d2x hseg
      tangentT := fun θ hθ => (norm_le_iff_forall_rowSum hbL).2 fun j => hF.bL θ (hs θ hθ) j
      normal := fun θ hθ => (norm_le_iff_forall_rowSum hbN).2 fun r => hF.bN θ (hs θ hθ) r
      normalT := fun θ hθ => (norm_le_iff_forall_rowSum hbNt).2 fun j => hF.bNt θ (hs θ hθ) j }

/-- **Soundness of route B at the refined data**, as `refinedBCore_sound`, at `FrameFactsLN`. -/
theorem refinedBCore_soundLN [LawfulCertArith α] (c : TorusCertificate n α) (w : RefinedBWit)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFactsLN c w.R)
    (h : refinedBCore n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedBCore, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hX, hwf⟩, hfit⟩, hini⟩, hok⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := w.num c.params c.freqBox with hQ
  have hN : (Q.toNum n).Wf := NumBQ.wfOk_sound hwf
  have hX' : (0 : ℝ) < w.core.Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hγq : 0 < c.params.γ := by exact_mod_cast S.hγ
  obtain ⟨hsm, hd2, hd3, hroom⟩ := finalB_sound (Q := Q) (iN := w.R.bN) B.hs rfl rfl hX hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hOk := NumBQ.okB_sound hN hok
  rw [← NumBQ.cast_capB, ← NumBQ.cast_initB] at hOk
  have hμ2 : (((c.params.μ / 2 : ℚ)) : ℝ) = (c.params.μ : ℝ) / 2 := by push_cast; ring
  rw [hμ2] at hOk
  have hIS : IsoStanding n (c.params.tau : ℝ) c.params.M c.params.σK c.params.σB c.params.σT
      c.params.σω c.params.nuRay ωstar c.D c.H c.params.γ :=
    { toParams := ⟨S.hn, S.hτ, S.hM, S.hσK, S.hσB, S.hσT⟩
      σω_gt := S.hσω
      ν_pos := S.hν
      ωstar_ne := hω0
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := B.hH.2
      gamma_pos := S.hγ
      dio := hdio }
  have hSv := (hIS.setting S.hs1.le).toStanding
  have hRef : RefHypB (Q.toNum n) ⟨w.R.bL, w.R.bN, w.R.bNt⟩ c.D c.H c.K (Q.toNum n).ρ :=
    refHypB_ofLN (NumBQ.one_le_n hN) rfl hρ0 rfl rfl
      (by show ((2 * w.R.dx : ℚ) : ℝ) = _; push_cast; ring)
      (by show ((2 * w.R.d2x : ℚ) : ℝ) = _; push_cast; ring) hopen
      (differentiableOn_fderiv_ham hSv) hH hF
  have hCt := NumBQ.cert_ray hN hsites htail hγq hω hdio
  have hν2' : (c.params.nuRay : ℝ) ≤
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖ - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_B
    (N := Q.toNum n) (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB)
    (σT := c.params.σT) (μ := c.params.μ) (γbar := c.params.γbar)
    (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖) (ν := c.params.nuRay)
    (Xs := w.core.Xs) (I := ⟨w.R.bL, w.R.bN, w.R.bNt⟩) (Ω := ray ωstar)
    hN rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by show ((c.params.σK - c.params.μ / 2 : ℚ) : ℝ) = _; push_cast; ring) hΘ
    (by show ((c.params.M * w.core.sN : ℚ) : ℝ) = _; push_cast; rfl)
    (NumBQ.initOk_sound hini) (NumBQ.fitsOk_sound hfit) hOk hX' hopen htransl hholo hper hreal
    B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hRef hH.d2h
    (fun t ht => ⟨t, ht, rfl⟩) hCt S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

/-- The test of route B at the refined data, without the torsion majorant. -/
def refinedBLNTest (c : TorusCertificate n α) (w : RefinedBWit) : Bool :=
  checkHamClaim c w.R && checkFrameLN c w.R.bL w.R.bN w.R.bNt &&
    refinedBCore n c.params c.freqBox w

/-- **The unused `bT` does not affect the test.** -/
theorem refinedBLNTest_bT (c : TorusCertificate n α) (w : RefinedBWit) (t : ℚ) :
    refinedBLNTest c { w with R := { w.R with bT := t } } = refinedBLNTest c w := rfl

/-- `checkFrameLN` at the claim as `FrameFactsLN`. -/
theorem frameFactsLN_of [LawfulCertArith α] {c : TorusCertificate n α} {R : RefClaim}
    (hs : checkStatic c = true) (h : checkFrameLN c R.bL R.bN R.bNt = true) : FrameFactsLN c R := by
  obtain ⟨h1, h2, h3⟩ := checkFrameLN_sound hs h
  exact ⟨h1, h2, h3⟩

/-- **The engine of route B at the refined data, without the torsion majorant.** -/
def routeBRefinedLN : EngineV2 where
  Wit := RefinedBWit
  test := fun c w => refinedBLNTest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBLNTest, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCore_soundLN c w hω hdio B (checkHamClaim_sound B.hs hH)
      (frameFactsLN_of B.hs hF) hc

/-- **Soundness of the certifier at `routeBRefinedLN`.** -/
theorem checkTorusCertificateV2_routeBRefinedLN_sound [LawfulCertArith α]
    {c : TorusCertificate n α} {w : RefinedBWit}
    (h : checkTorusCertificateV2 routeBRefinedLN c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateV2_sound routeBRefinedLN h hω hdio

/-- **Every witness `routeBRefined` accepts, `routeBRefinedLN` accepts.** -/
theorem refinedBLNTest_of_refinedBTest (c : TorusCertificate n α) (w : RefinedBWit)
    (h : refinedBTest c w = true) : refinedBLNTest c w = true := by
  simp only [refinedBTest, refinedBLNTest, checkFrameMajorants, checkFrameLN, RefClaim.frame,
    Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hH, ⟨⟨⟨hL, hN⟩, -⟩, -⟩⟩, hc⟩ := h
  exact ⟨⟨hH, hL, hN⟩, hc⟩

end KAM.CertificateSharp.V2

end
