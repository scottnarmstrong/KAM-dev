/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBCore
public import KAM.Iso.Sharp2.RouteB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Route B at the refined data

`refinedBCore_sound` concludes `CertifiedTorus` from `BaseFacts`, `HamFacts`, `FrameFacts` and the
numerical test `refinedBCore`, through the route-B branch `iso_g1_branch_B` (as stage 2 of route A
goes through `iso_g1_branch_A`: the wrapper's `max {C₂♯, c2B}` would leave a useless displacement
near a refined threshold).

* `norm_hamComm_sub_le_of`: `|Δ(A Ω₀ - Ω₀ A)| ≤ 2 d |Δz|` on a segment in `D`, from the claimed
  `|D²X_H| ≤ d` (the frozen form `norm_hamComm_sub_le` uses `M`);
* `refHypB_of`: `RefHypB` from the claimed bounds, with `c_Th = 2 d_X`, `c_DTh = 2 d_{2X}`;
* `finalB_sound`: the smallness, the two displacements and the room of the ray.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Iso.Sharp2.RouteB KAM.Iso.Apost

variable {n : ℕ}

/-- `|Δ(A Ω₀ - Ω₀ A)| ≤ 2 d |Δz|` on a segment in `D`, from `|D²X_h| ≤ d` on `D`. -/
theorem norm_hamComm_sub_le_of {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {d : ℝ} (hopen : IsOpen D)
    (hdiff : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) D)
    (hb : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ d)
    {z z' : (Fin n → ℂ) × (Fin n → ℂ)} (hseg : segment ℝ z z' ⊆ D) :
    ‖hamComm h z - hamComm h z'‖ ≤ 2 * d * ‖z - z'‖ := by
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (f := fderiv ℂ (hamiltonianVectorFieldℂ h)) (s := segment ℝ z' z)
    (fun x hx => hdiff.differentiableAt (hopen.mem_nhds (hseg (segment_symm ℝ z z' ▸ hx))))
    (fun x hx => by
      rw [norm_fderiv_fderiv_eq]
      exact hb x (hseg (segment_symm ℝ z z' ▸ hx)))
    (convex_segment z' z) (left_mem_segment ℝ z' z) (right_mem_segment ℝ z' z)
  have e : hamComm h z - hamComm h z' =
      sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z - fderiv ℂ (hamiltonianVectorFieldℂ h) z') *
          omegaZeroMatrix n -
        omegaZeroMatrix n *
          sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z -
            fderiv ℂ (hamiltonianVectorFieldℂ h) z') := by
    rw [PerturbationAux.sqMat_sub]
    unfold hamComm
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul, norm_sqMat]
  linarith

variable {α : Type} [CertArith α]

/-- `RefHypB` from the claimed bounds, for numbers with `M₁ = d_X`, `M₂ = d_{2X}`,
`c_Th = 2 d_X`, `c_DTh = 2 d_{2X}` and the initial values `b_L, b_N, b_{Nᵀ}` of the claim. -/
theorem refHypB_of {N : NumB n} {c : TorusCertificate n α} {R : RefClaim} {ωstar : Fin n → ℝ}
    (hn : 1 ≤ n) (hρ : N.ρ = c.params.rho) (hρ0 : (0 : ℝ) < c.params.rho)
    (hM1 : N.M1 = R.dx) (hM2 : N.M2 = R.d2x) (hcTh : N.cTh = 2 * R.dx)
    (hcDTh : N.cDTh = 2 * R.d2x) (hopen : IsOpen c.D)
    (hdiff : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ c.H)) c.D)
    (hH : HamFacts c R) (hF : FrameFacts c R ωstar) :
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

/-- **`finalB` gives the smallness, the two displacements and the room of the ray.** -/
theorem finalB_sound [LawfulCertArith α] {c : TorusCertificate n α} {Q : NumBQ}
    {iLt iN iNt Xs : ℚ} (hs : checkStatic c = true) (hτ : Q.τ = c.params.tau)
    (hρ : Q.ρ = c.params.rho) (hXs : 0 < Xs) (h : finalB Q n c.params c.freqBox iLt iNt Xs = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    c1B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs * c.params.err /
        ((c.params.γ : ℝ) ^ 4 * (Q.toNum n).ρ ^ (4 * (Q.toNum n).τ)) < 1 ∧
      c2B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs * c.params.err /
        ((c.params.γ : ℝ) ^ 2 * (Q.toNum n).ρ ^ (2 * (Q.toNum n).τ)) ≤ c.params.disp ∧
      c3B (Q.toNum n) ⟨iLt, iN, iNt⟩ Xs * c.params.err /
        ((c.params.γ : ℝ) ^ 2 * (Q.toNum n).ρ ^ (2 * (Q.toNum n).τ)) ≤ c.params.disp ∧
      (c.params.disp : ℝ) < ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := by
  have S := checkStatic_sound hs
  simp only [finalB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have _hXs := hXs
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have e4 : (Q.toNum n).ρ ^ (4 * (Q.toNum n).τ) = ((c.params.rho ^ (4 * c.params.tau) : ℚ) : ℝ) := by
    have e : (4 * ((Q.τ : ℕ) : ℝ)) = ((4 * Q.τ : ℕ) : ℝ) := by push_cast; ring
    rw [NumBQ.cast_τ, e, Real.rpow_natCast]
    show ((Q.ρ : ℚ) : ℝ) ^ (4 * Q.τ) = _
    rw [hρ, hτ]; push_cast; rfl
  have e2 : (Q.toNum n).ρ ^ (2 * (Q.toNum n).τ) = ((c.params.rho ^ (2 * c.params.tau) : ℚ) : ℝ) := by
    have e : (2 * ((Q.τ : ℕ) : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
    rw [NumBQ.cast_τ, e, Real.rpow_natCast]
    show ((Q.ρ : ℚ) : ℝ) ^ (2 * Q.τ) = _
    rw [hρ, hτ]; push_cast; rfl
  have hg4 : (0 : ℝ) < (c.params.γ : ℝ) ^ 4 * ((c.params.rho ^ (4 * c.params.tau) : ℚ) : ℝ) := by
    have := S.hγ; push_cast; positivity
  have hg2 : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * ((c.params.rho ^ (2 * c.params.tau) : ℚ) : ℝ) := by
    have := S.hγ; push_cast; positivity
  have hb := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at hb
  have hclose : ∀ {C B : ℝ}, C ≤ B → B * c.params.err ≤ c.params.disp *
      ((c.params.γ : ℝ) ^ 2 * ((c.params.rho : ℝ) ^ (2 * c.params.tau))) →
      C * c.params.err / ((c.params.γ : ℝ) ^ 2 *
        ((c.params.rho ^ (2 * c.params.tau) : ℚ) : ℝ)) ≤ c.params.disp := fun {C B} hC hB => by
    rw [div_le_iff₀ hg2]
    push_cast
    exact (mul_le_mul_of_nonneg_right hC S.he0).trans hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e4, div_lt_one hg4, NumBQ.cast_c1B]
    have := (Rat.cast_lt (K := ℝ)).mpr h1
    push_cast at this ⊢
    exact this
  · rw [e2, NumBQ.cast_c2B]
    exact hclose (le_max_left _ _) hb
  · rw [e2, NumBQ.cast_c3B]
    exact hclose (le_max_right _ _) hb
  · have hlen : c.freqBox.length = n := by
      simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hs
      exact hs.1
    have hle := freqNormLo_le_norm hlen hω
    have h3' := (Rat.cast_lt (K := ℝ)).mpr h3
    push_cast at h3'
    have hp : (0 : ℝ) ≤ (c.params.σω : ℝ) - c.params.s := by linarith [S.hsσ]
    exact h3'.trans_le (mul_le_mul_of_nonneg_left hle hp)

variable [LawfulCertArith α]

/-- **Soundness of route B at the refined data**, through `iso_g1_branch_B`. -/
theorem refinedBCore_sound (c : TorusCertificate n α) (w : RefinedBWit) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
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
    refHypB_of (NumBQ.one_le_n hN) rfl hρ0 rfl rfl
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

end KAM.CertificateSharp.V2

end
