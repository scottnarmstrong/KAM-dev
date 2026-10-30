/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryCorrection
public import KAM.Sharp2.L1.NormsCauchy
public import KAM.Sharp2.RouteA.Frames
public import KAM.Apost.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The frames of the new torus after the ℓ¹ entry step (package B10c)

Blueprint `bp:p2s2l1:frame` of `blueprint/parts/p2s2-l1hybrid.tex`:

* `frames_barG`: B9's `KAM.Sharp2.RouteA.frames_bar` at a point, with the increments
  `|L̄ - L| ≤ a_L`, `|(L̄ - L)ᵀ| ≤ a_{Lᵀ}` as inputs (B9 has `a_L = n D`, `a_{Lᵀ} = 2n D`): the Gram
  increment is `σ_{Lᵀ} a_L + σ_K a_{Lᵀ}`, and `|B̄ - B| ≤ r_B`, `|N̄ - N| ≤ σ_B a_L + σ_K r_B`,
  `|N̄ᵀ - Nᵀ| ≤ r_B σ_{Lᵀ} + σ_B a_{Lᵀ}`, `r_B = σ_B² (σ_{Lᵀ} a_L + σ_K a_{Lᵀ})/(1 - ϑ)`;
* `l1_frame_increment`: with the frame certificate `‖L‖_{1,r} ≤ ν_K`, `‖N‖_{1,r} ≤ ν_N` and the ℓ¹
  bounds `A`, `B` of `ξᴸ`, `ξᴺ`, the correction `ΔK = L ξᴸ + N ξᴺ` has
  `‖ΔK‖_{1,r-2δ} ≤ ν_K A + ν_N B`,
  and the row-sum ℓ¹ Cauchy estimate gives on `T_{r-3δ}`
  `|DK̄ - DK| ≤ (ν_K A + ν_N B)/(e δ)` and `|(L̄ - L)ᵀ| ≤ 2n (ν_K A + ν_N B)/(e δ)`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

variable {n : ℕ}

/-- The frame increments of `K'` over `K` at `θ`, with general rates. -/
structure BarBdG (K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (aL aLt aB aN aNt : ℝ) : Prop where
  dDK : ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ aL
  dLt : ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ aLt
  unit : IsUnit (gramMatrix K' θ).det
  dB : ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ aB
  dN : ‖normalMat K' θ - normalMat K θ‖ ≤ aN
  dNt : ‖(normalMat K' θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ aNt

/-- `r_B = σ_B² (σ_{Lᵀ} a_L + σ_K a_{Lᵀ})/(1 - ϑ)`. -/
def rBOf (p : StepInA) (aL aLt : ℝ) : ℝ := p.sB ^ 2 * (p.sLt * aL + p.sK * aLt) / (1 - p.th)

/-- Lever L8 at a point, with general increments of `L`, `Lᵀ`. -/
theorem frames_barG {p : StepInA} (hp : p.Pos) {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} {mLt mB aL aLt : ℝ}
    (hLθ : ‖tangentMat K θ‖ ≤ p.sK) (hGu : IsUnit (gramMatrix K θ).det)
    (hBθ : ‖(gramMatrix K θ)⁻¹‖ ≤ mB) (hLtθ : ‖(tangentMat K θ)ᵀ‖ ≤ mLt)
    (hmLt : mLt ≤ p.sLt) (hmB : mB ≤ p.sB)
    (hdL : ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ aL)
    (hdLt : ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ aLt)
    (hgr : p.sB * (p.sLt * aL + p.sK * aLt) ≤ p.th)
    (hcLt : mLt + aLt ≤ p.sLt) (hcB : mB + rBOf p aL aLt ≤ p.sB) :
    BarBdG K K' θ aL aLt (rBOf p aL aLt) (p.sB * aL + p.sK * rBOf p aL aLt)
      (rBOf p aL aLt * p.sLt + p.sB * aLt) := by
  have haL : 0 ≤ aL := (norm_nonneg _).trans hdL
  have haLt : 0 ≤ aLt := (norm_nonneg _).trans hdLt
  have hdL' : ‖tangentMat K' θ - tangentMat K θ‖ ≤ aL := by
    rw [PerturbationAux.norm_tangentMat_sub]; exact hdL
  have hLt' : ‖(tangentMat K' θ)ᵀ‖ ≤ p.sLt := by
    have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
      rw [Matrix.transpose_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans ((add_le_add hLtθ hdLt).trans hcLt)
  have hGd : ‖gramMatrix K' θ - gramMatrix K θ‖ ≤ p.sLt * aL + p.sK * aLt := by
    rw [PerturbationAux.gramMatrix_sub]
    calc _ ≤ ‖(tangentMat K' θ)ᵀ‖ * ‖tangentMat K' θ - tangentMat K θ‖ +
          ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ * ‖tangentMat K θ‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.linfty_opNorm_mul _ _)
            (Matrix.linfty_opNorm_mul _ _))
      _ ≤ p.sLt * aL + aLt * p.sK :=
          add_le_add (mul_le_mul hLt' hdL' (norm_nonneg _) hp.sLt)
            (mul_le_mul hdLt hLθ (norm_nonneg _) haLt)
      _ = p.sLt * aL + p.sK * aLt := by ring
  have hBθ' : ‖(gramMatrix K θ)⁻¹‖ ≤ p.sB := hBθ.trans hmB
  have hA : IsUnit (gramMatrix K θ) := (Matrix.isUnit_iff_isUnit_det _).2 hGu
  have hsmall : ‖(gramMatrix K θ)⁻¹‖ * ‖gramMatrix K' θ - gramMatrix K θ‖ ≤ p.th :=
    (mul_le_mul hBθ' hGd (norm_nonneg _) hp.sB).trans hgr
  obtain ⟨hU, -, hBdiff⟩ := neumann_ratio hA hp.th1 hsmall
  rw [add_sub_cancel] at hU hBdiff
  have hth := hp.one_sub_th
  have hdB : ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ rBOf p aL aLt := by
    have hBB : ‖(gramMatrix K θ)⁻¹‖ ^ 2 ≤ p.sB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hBθ' 2
    calc _ ≤ ‖(gramMatrix K θ)⁻¹‖ ^ 2 * ‖gramMatrix K' θ - gramMatrix K θ‖ / (1 - p.th) := hBdiff
      _ ≤ p.sB ^ 2 * (p.sLt * aL + p.sK * aLt) / (1 - p.th) :=
          div_le_div_of_nonneg_right (mul_le_mul hBB hGd (norm_nonneg _) (by positivity)) hth.le
      _ = rBOf p aL aLt := rfl
  have hrB : 0 ≤ rBOf p aL aLt := (norm_nonneg _).trans hdB
  have hB' : ‖(gramMatrix K' θ)⁻¹‖ ≤ p.sB := (norm_le_add_sub hBθ hdB).trans hcB
  have hdN : ‖normalMat K' θ - normalMat K θ‖ ≤ p.sB * aL + p.sK * rBOf p aL aLt := by
    rw [PerturbationAux.normalMat_sub]
    have a1 : ‖omegaZeroMatrix n * (tangentMat K' θ - tangentMat K θ) *
        (gramMatrix K' θ)⁻¹‖ ≤ aL * p.sB := by
      refine FrameSharp.norm_mul_le_of_le ?_ hB'
      rw [norm_omegaZeroMatrix_mul]
      exact hdL'
    have a2 : ‖omegaZeroMatrix n * tangentMat K θ *
        ((gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹)‖ ≤ p.sK * rBOf p aL aLt := by
      refine FrameSharp.norm_mul_le_of_le ?_ hdB
      rw [norm_omegaZeroMatrix_mul]
      exact hLθ
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ aL * p.sB + p.sK * rBOf p aL aLt := add_le_add a1 a2
      _ = p.sB * aL + p.sK * rBOf p aL aLt := by ring
  have hdNt : ‖(normalMat K' θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ rBOf p aL aLt * p.sLt + p.sB * aLt := by
    rw [← norm_mul_omegaZeroMatrix, Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
      TorsionPoly.normalMat_transpose_mul_omega]
    have hdLt'' : ‖(tangentMat K' θ)ᵀ - (tangentMat K θ)ᵀ‖ ≤ aLt := by
      rw [← Matrix.transpose_sub]; exact hdLt
    calc _ ≤ ‖(gramMatrix K' θ)⁻¹‖ * ‖(tangentMat K' θ)ᵀ - (tangentMat K θ)ᵀ‖ +
          ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ * ‖(tangentMat K θ)ᵀ‖ :=
          norm_mul_sub_mul_le _ _ _ _
      _ ≤ p.sB * aLt + rBOf p aL aLt * p.sLt :=
          add_le_add (mul_le_mul hB' hdLt'' (norm_nonneg _) hp.sB)
            (mul_le_mul hdB (hLtθ.trans hmLt) (norm_nonneg _) hrB)
      _ = rBOf p aL aLt * p.sLt + p.sB * aLt := by ring
  exact ⟨hdL, hdLt, (Matrix.isUnit_iff_isUnit_det _).1 hU, hdB, hdN, hdNt⟩

variable {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- The ℓ¹ frame increment: on `T_{r-3δ}`, `|DK̄ - DK| ≤ (ν_K A + ν_N B)/(e δ)` and
`|(L̄ - L)ᵀ| ≤ 2n (ν_K A + ν_N B)/(e δ)` for `K̄ = newtonMap h K ω (r - 2δ)`. -/
theorem l1_frame_increment (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r β ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : Admissible σK σB σT 𝔅 h ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h3δ : 3 * δ < r) {νK νN A B : ℝ}
    (hLK : L1Mat r (tangentMat K) νK) (hNK : L1Mat r (normalMat K) νN)
    (hXLd : DifferentiableOn ℂ (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - 2 * δ)))
    (hXLp : IsPeriodicOn (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - 2 * δ))
    (hXNd : DifferentiableOn ℂ (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - δ)))
    (hXNp : IsPeriodicOn (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - δ))
    (hXL : L1Vec (r - 2 * δ) (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) A)
    (hXN : L1Vec (r - δ) (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) B) :
    ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
        (νK * A + νN * B) / (Real.exp 1 * δ) ∧
      ‖(tangentMat (newtonMap h K ω (r - 2 * δ)) θ - tangentMat K θ)ᵀ‖ ≤
        2 * n * (νK * A + νN * B) / (Real.exp 1 * δ) := by
  have hr := hK.r_pos
  have h2δ : 2 * δ < r := by linarith
  have hr2 : 0 < r - 2 * δ := by linarith
  have hsub2r : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub21 : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨hLd, -, -, -, -, -, hNd, -, -, -, -, -, -, -, -⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨⟨hLp, -⟩, hperiod, -⟩ := periodicity hS hr hK.holo hK.primary hK𝔅
  obtain ⟨-, hNp, -⟩ := hperiod hGu
  obtain ⟨⟨-, -, -, hcd, hcp, -⟩, -⟩ := correction_spec hS hK hδ hδ1 h2δ
  -- `ΔK = L ξᴸ + N ξᴺ` in ℓ¹ on `T_{r-2δ}`
  have hfeq : ∀ θ, sumVec n (correction h K ω θ) =
      tangentMat K θ *ᵥ triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ +
        normalMat K θ *ᵥ triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ := fun θ => by
    rw [Correction.sumVec_correction]
    unfold frameMat
    rw [show xi h K ω θ = Sum.elim (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ)
      (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) from rfl,
      Matrix.fromCols_mulVec_sumElim]
  have hfd : DifferentiableOn ℂ (fun θ => sumVec n (correction h K ω θ))
      (complexStrip n (r - 2 * δ)) :=
    (sumVecIso n).differentiable.comp_differentiableOn hcd
  have hfp : IsPeriodicOn (fun θ => sumVec n (correction h K ω θ)) (r - 2 * δ) :=
    fun j z hz => by simp only [hcp j z hz]
  have hLd2 := hLd.mono hsub2r
  have hNd2 := hNd.mono hsub2r
  have h1 := L1Mat.mulVec hr2 hLd2 (fun j z hz => hLp j z (hsub2r hz)) hXLd hXLp
    (hLK.mono (by linarith)) hXL
  have h2 := L1Mat.mulVec hr2 hNd2 (fun j z hz => hNp j z (hsub2r hz)) (hXNd.mono hsub21)
    (fun j z hz => hXNp j z (hsub21 hz)) (hNK.mono (by linarith))
    (L1Vec.mono hr2.le (by linarith) hXN)
  have h3 := L1Vec.add hr2 (hLd2.matrix_mulVec hXLd) (hNd2.matrix_mulVec (hXNd.mono hsub21)) h1 h2
  have hfl1 : L1Vec (r - 2 * δ) (fun θ => sumVec n (correction h K ω θ)) (νK * A + νN * B) :=
    L1Vec.congr_real (fun x => (hfeq _).symm) h3
  -- the row-sum Cauchy estimates
  intro θ hθ
  have hθ' : θ ∈ complexStrip n (r - 2 * δ - δ) := by
    rwa [show r - 2 * δ - δ = r - 3 * δ by ring]
  have hθ2 : θ ∈ complexStrip n (r - 2 * δ) := Triangular.strip_mono (by linarith) hθ
  have hθr := hsub2r hθ2
  have hδr2 : δ < r - 2 * δ := by linarith
  have hjac := L1Vec.norm_jac_le hδ hδr2 hfd hfp hfl1 θ hθ'
  have hjacT := L1Vec.norm_jac_transpose_le hδ hδr2 hfd hfp hfl1 θ hθ'
  have hK'eq : fderiv ℂ (newtonMap h K ω (r - 2 * δ)) θ =
      fderiv ℂ K θ + fderiv ℂ (correction h K ω) θ := by
    rw [(NewtonError.newtonMap_eventuallyEq hθ2).fderiv_eq]
    exact fderiv_add (hK.holo.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr))
      (hcd.differentiableAt ((isOpen_complexStrip n _).mem_nhds hθ2))
  have hmat : jac (fun θ => sumVec n (correction h K ω θ)) θ =
      tangentMat (newtonMap h K ω (r - 2 * δ)) θ - tangentMat K θ := by
    ext s j
    rw [jac, Matrix.of_apply, fderiv_sumVec_apply, Matrix.sub_apply, tangentMat_apply,
      tangentMat_apply, hK'eq]
    simp
  rw [hmat] at hjac hjacT
  rw [Fintype.card_sum, Fintype.card_fin] at hjacT
  refine ⟨?_, hjacT.trans_eq (by push_cast; ring)⟩
  rw [← PerturbationAux.norm_tangentMat_sub]
  exact hjac

end KAM.Sharp2.L1

end
