/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Step
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The frames of the new torus (`bp:p2s2hc:frames`)

At a point where `G` is invertible, with `ΔL = DΔK`, `g = ℓᵗ d₁ + d₁ᵗ ℓ + d₁ᵗ d₁` and `β g < 1`:
`G₁ = G (1 + B (G₁ - G))` is invertible by Neumann (`neumann_ratio`), and the frames of
`K₁ = K + ΔK` are explicit:

* `gram_step_sub`: `G₁ - G = Lᵀ ΔL + ΔLᵀ L + ΔLᵀ ΔL`;
* `normalMat_step_sub`: `N₁ - N = Ω₀ (ΔL B₁ + L (B₁ - B))`;
* `normalMat_transpose_step_sub`: `(N₁ᵀ - Nᵀ) Ω₀ = B₁ ΔLᵀ + (B₁ - B) Lᵀ`;
* `frames_step`: every bound of Lemma `bp:p2s2hc:frames`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

/-- The numbers of Lemma `bp:p2s2hc:frames`: initial values of `K` and the increments of `DΔK`. -/
structure FrameNum where
  ℓ : ℝ
  ℓt : ℝ
  β : ℝ
  ν : ℝ
  νt : ℝ
  d1 : ℝ
  d1t : ℝ

namespace FrameNum

variable (F : FrameNum)

/-- `g = ℓᵗ d₁ + d₁ᵗ ℓ + d₁ᵗ d₁ ≥ |G₁ - G|`. -/
def g : ℝ := F.ℓt * F.d1 + F.d1t * F.ℓ + F.d1t * F.d1
/-- `β₁ = β/(1 - βg) ≥ |B₁|`. -/
def β1 : ℝ := F.β / (1 - F.β * F.g)
/-- `b = β² g/(1 - βg) ≥ |B₁ - B|`. -/
def b : ℝ := F.β ^ 2 * F.g / (1 - F.β * F.g)
/-- `n_Δ = β₁ d₁ + ℓ b ≥ |N₁ - N|`. -/
def nΔ : ℝ := F.β1 * F.d1 + F.ℓ * F.b
/-- `n_Δᵗ = β₁ d₁ᵗ + ℓᵗ b ≥ |N₁ᵀ - Nᵀ|`. -/
def nΔt : ℝ := F.β1 * F.d1t + F.ℓt * F.b

end FrameNum

/-- `‖Y‖ ≤ ‖X‖ + ‖Y - X‖`, in a form for bounds. -/
theorem norm_le_add_of_sub {ι κ : Type*} [Fintype ι] [Fintype κ] {X Y : Matrix ι κ ℂ} {a b : ℝ}
    (hX : ‖X‖ ≤ a) (hd : ‖Y - X‖ ≤ b) : ‖Y‖ ≤ a + b := by
  have e : Y = X + (Y - X) := by rw [add_sub_cancel]
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add hX hd)

/-- Step `step:p2s2hc:fr-g`: `G₁ - G = Lᵀ ΔL + ΔLᵀ L + ΔLᵀ ΔL`. -/
theorem gram_step_sub {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    gramMatrix (K + ΔK) θ = gramMatrix K θ +
      ((tangentMat K θ)ᵀ * tangentMat ΔK θ + (tangentMat ΔK θ)ᵀ * tangentMat K θ +
        (tangentMat ΔK θ)ᵀ * tangentMat ΔK θ) := by
  rw [gramMatrix_eq_tangentMat_transpose_mul, gramMatrix_eq_tangentMat_transpose_mul,
    tangentMat_add_step hK hΔ, Matrix.transpose_add]
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

/-- Step `step:p2s2hc:fr-nf`: `N₁ - N = Ω₀ (ΔL B₁ + L (B₁ - B))`. -/
theorem normalMat_step_sub {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    normalMat (K + ΔK) θ - normalMat K θ = omegaZeroMatrix n *
      (tangentMat ΔK θ * (gramMatrix (K + ΔK) θ)⁻¹ +
        tangentMat K θ * ((gramMatrix (K + ΔK) θ)⁻¹ - (gramMatrix K θ)⁻¹)) := by
  simp only [normalMat, tangentMat_add_step hK hΔ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_assoc]
  abel

/-- Step `step:p2s2hc:fr-nf`: `(N₁ᵀ - Nᵀ) Ω₀ = B₁ ΔLᵀ + (B₁ - B) Lᵀ`. -/
theorem normalMat_transpose_step_sub {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ) :
    ((normalMat (K + ΔK) θ)ᵀ - (normalMat K θ)ᵀ) * omegaZeroMatrix n =
      (gramMatrix (K + ΔK) θ)⁻¹ * (tangentMat ΔK θ)ᵀ +
        ((gramMatrix (K + ΔK) θ)⁻¹ - (gramMatrix K θ)⁻¹) * (tangentMat K θ)ᵀ := by
  rw [Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
    TorsionPoly.normalMat_transpose_mul_omega, tangentMat_add_step hK hΔ, Matrix.transpose_add]
  simp only [Matrix.mul_add, Matrix.sub_mul]
  abel

/-- Lemma `bp:p2s2hc:frames` (pointwise). -/
theorem frames_step {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    {F : FrameNum} (hK : DifferentiableAt ℂ K θ) (hΔ : DifferentiableAt ℂ ΔK θ)
    (hG : IsUnit (gramMatrix K θ).det) (hL : ‖tangentMat K θ‖ ≤ F.ℓ)
    (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ F.ℓt) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ F.β)
    (hN : ‖normalMat K θ‖ ≤ F.ν) (hNt : ‖(normalMat K θ)ᵀ‖ ≤ F.νt)
    (h1 : ‖tangentMat ΔK θ‖ ≤ F.d1) (h1t : ‖(tangentMat ΔK θ)ᵀ‖ ≤ F.d1t)
    (hs : F.β * F.g < 1) :
    IsUnit (gramMatrix (K + ΔK) θ).det ∧ ‖(tangentMat (K + ΔK) θ)ᵀ‖ ≤ F.ℓt + F.d1t ∧
      ‖(gramMatrix (K + ΔK) θ)⁻¹‖ ≤ F.β1 ∧
      ‖(gramMatrix (K + ΔK) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ F.b ∧
      ‖normalMat (K + ΔK) θ - normalMat K θ‖ ≤ F.nΔ ∧
      ‖(normalMat (K + ΔK) θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ F.nΔt ∧
      ‖normalMat (K + ΔK) θ‖ ≤ F.ν + F.nΔ ∧ ‖(normalMat (K + ΔK) θ)ᵀ‖ ≤ F.νt + F.nΔt := by
  have nm := @FrameSharp.norm_mul_le_of_le
  set L := tangentMat K θ with hLdef
  set dL := tangentMat ΔK θ with hdL
  have hβ : 0 ≤ F.β := (norm_nonneg _).trans hB
  have hg : ‖Lᵀ * dL + dLᵀ * L + dLᵀ * dL‖ ≤ F.g :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (nm hLt h1) (nm h1t hL))) (nm h1t h1))
  have hq : 0 < 1 - F.β * F.g := by linarith
  have hsmall : ‖(gramMatrix K θ)⁻¹‖ * ‖Lᵀ * dL + dLᵀ * L + dLᵀ * dL‖ ≤ F.β * F.g :=
    mul_le_mul hB hg (norm_nonneg _) hβ
  obtain ⟨hu, hb1, hb2⟩ := neumann_ratio ((Matrix.isUnit_iff_isUnit_det _).2 hG) hs hsmall
  rw [← gram_step_sub hK hΔ] at hu hb1 hb2
  have hB₁ : ‖(gramMatrix (K + ΔK) θ)⁻¹‖ ≤ F.β1 :=
    hb1.trans (div_le_div_of_nonneg_right hB hq.le)
  have hdB : ‖(gramMatrix (K + ΔK) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ F.b :=
    hb2.trans (div_le_div_of_nonneg_right (mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) hB 2) hg (norm_nonneg _) (sq_nonneg _)) hq.le)
  have hdN : ‖normalMat (K + ΔK) θ - normalMat K θ‖ ≤ F.nΔ := by
    rw [normalMat_step_sub hK hΔ, norm_omegaZeroMatrix_mul]
    refine ((norm_add_le _ _).trans (add_le_add (nm h1 hB₁) (nm hL hdB))).trans (le_of_eq ?_)
    rw [FrameNum.nΔ]
    ring
  have hdNt : ‖(normalMat (K + ΔK) θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ F.nΔt := by
    rw [← norm_mul_omegaZeroMatrix, normalMat_transpose_step_sub hK hΔ]
    refine ((norm_add_le _ _).trans (add_le_add (nm hB₁ h1t) (nm hdB hLt))).trans (le_of_eq ?_)
    rw [FrameNum.nΔt]
    ring
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hu, ?_, hB₁, hdB, hdN, hdNt,
    norm_le_add_of_sub hN hdN, norm_le_add_of_sub hNt hdNt⟩
  rw [tangentMat_add_step hK hΔ, Matrix.transpose_add]
  exact (norm_add_le _ _).trans (add_le_add hLt h1t)

end KAM.Sharp2.Hybrid

end
