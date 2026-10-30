/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Frame

/-!
# Refined data of the v2 a-posteriori theorem

Blueprint `bp:p2s2:standing` (R1)–(R2) and `bp:p2s2:defaults`: separate Hamiltonian bounds `M₁`,
`M₂` and caps `σ_{Lᵀ}`, `σ_N`, `σ_{Nᵀ}` of the frame objects `Lᵀ`, `N`, `Nᵀ`.

* `RefData`, `RefData.ofV1`: the data and the v1 values;
* `RefHyp`: the hypotheses, bounds on explicit objects of `h` and `K`;
* `refHyp_ofV1`: the frozen hypotheses (with margin `μ`) imply `RefHyp` at the v1 values.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp2

open KAM.Torus KAM.Apost

/-- The refined data `(R1)`–`(R2)` of `bp:p2s2:standing`: separate Hamiltonian bounds and caps of
`Lᵀ, N, Nᵀ`. -/
structure RefData where
  M1 : ℝ
  M2 : ℝ
  sLt : ℝ
  sN : ℝ
  sNt : ℝ

/-- The v1 values (`bp:p2s2:defaults`). -/
def RefData.ofV1 (n : ℕ) (M σK σB : ℝ) : RefData := ⟨M, M, 2 * n * σK, σK * σB, 2 * n * σK * σB⟩

/-- The refined hypotheses: bounds on explicit objects of `h` and `K` (a certificate checks them).
-/
structure RefHyp {n : ℕ} (rd : RefData) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ρ : ℝ) : Prop where
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ rd.M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ rd.M2
  tangentT : ∀ θ ∈ complexStrip n ρ, ‖(tangentMat K θ)ᵀ‖ ≤ rd.sLt
  normal : ∀ θ ∈ complexStrip n ρ, ‖normalMat K θ‖ ≤ rd.sN
  normalT : ∀ θ ∈ complexStrip n ρ, ‖(normalMat K θ)ᵀ‖ ≤ rd.sNt

/-- Blueprint `bp:p2s2:defaults`: the frozen hypotheses imply the refined ones with the v1
values. -/
theorem refHyp_ofV1 {n : ℕ} (hn : 1 ≤ n) {M σK σB μ ρ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hDK : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB - μ) :
    RefHyp (RefData.ofV1 n M (σK - μ) (σB - μ)) 𝔅 h K ρ := by
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨fun z hz => (hbd z hz).1, fun z hz => (hbd z hz).2, fun θ hθ => ?_, fun θ hθ => ?_,
    fun θ hθ => ?_⟩
  · have h1 : ‖tangentMat K θ‖ ≤ σK - μ := (FrameAux.norm_tangentMat K θ).le.trans (hDK θ hθ)
    exact (FrameAux.norm_transpose_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left h1 (by positivity))
  · have h1 : ‖tangentMat K θ‖ ≤ σK - μ := (FrameAux.norm_tangentMat K θ).le.trans (hDK θ hθ)
    unfold normalMat
    refine (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul ?_ (hG θ hθ).2 (norm_nonneg _)
      ((norm_nonneg _).trans h1))
    rw [norm_omegaZeroMatrix_mul]
    exact h1
  · have h1 : ‖tangentMat K θ‖ ≤ σK - μ := (FrameAux.norm_tangentMat K θ).le.trans (hDK θ hθ)
    have h3 : ‖normalMat K θ‖ ≤ (σK - μ) * (σB - μ) := by
      unfold normalMat
      refine (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul ?_ (hG θ hθ).2 (norm_nonneg _)
        ((norm_nonneg _).trans h1))
      rw [norm_omegaZeroMatrix_mul]
      exact h1
    refine (FrameAux.norm_transpose_le_two_mul _).trans ?_
    show _ ≤ 2 * n * (σK - μ) * (σB - μ)
    rw [mul_assoc (2 * (n : ℝ))]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)

end KAM.Sharp2

end
