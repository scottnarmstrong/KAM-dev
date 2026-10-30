/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.PerturbationTorsion
public import KAM.Uniq.Frame
public import KAM.Matrix.Bridges
public import KAM.Apost.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parameter boxes: the torsion under a change of the Hamiltonian

For a fixed torus `K` and frequency `ω`, the torsion `T = Nᵀ Ω₀ (A N - ∂_ω N)` depends on the
Hamiltonian only through `A = DX_h ∘ K`, and `N` depends on `K` only. Hence
`T_{h'} - T_h = Nᵀ Ω₀ (A' - A) N` (`KAM.Sharp.torsion_sub_param`), and the averaged torsion moves
  by at
most `2 n (σ_K' σ_B')² ℓ` when `‖DX_{h'} - DX_h‖ ≤ ℓ` on the torus
  (`KAM.Sharp.norm_torsionAverage_sub_param_le`).
-/

public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-- `T_{h'} - T_h = Nᵀ Ω₀ (A' - A) N` for a fixed torus and frequency. -/
theorem torsion_sub_param (h h' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {θ : Fin n → ℂ}
    (hN : DifferentiableAt ℂ (normalMat K) θ) :
    torsion h' K ω θ - torsion h K ω θ = (normalMat K θ)ᵀ * omegaZeroMatrix n *
      ((linMat h' K θ - linMat h K θ) * normalMat K θ) := by
  rw [torsion_eq_mat h' K ω hN, torsion_eq_mat h K ω hN, ← Matrix.mul_sub]
  congr 1
  simp only [normalFieldMat]
  rw [Matrix.sub_mul]
  abel

/-- The pointwise estimate `‖T_{h'} - T_h‖ ≤ 2 n (a b)² ℓ`, from `‖DK‖ ≤ a`, `‖G⁻¹‖ ≤ b` and
`‖DX_{h'}(Kθ) - DX_h(Kθ)‖ ≤ ℓ`. -/
theorem norm_torsion_sub_param_le (h h' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {θ : Fin n → ℂ}
    (hN : DifferentiableAt ℂ (normalMat K) θ) {a b ℓ : ℝ}
    (hL : ‖fderiv ℂ K θ‖ ≤ a) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ b)
    (hDX : ‖fderiv ℂ (hamiltonianVectorFieldℂ h') (K θ) -
      fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)‖ ≤ ℓ) :
    ‖torsion h' K ω θ - torsion h K ω θ‖ ≤ 2 * n * (a * b) ^ 2 * ℓ := by
  have hNb : ‖normalMat K θ‖ ≤ a * b := Uniq.FrameAux.norm_normalMat_le' hL hB
  have hab : 0 ≤ a * b := (norm_nonneg _).trans hNb
  have hΔ : ‖linMat h' K θ - linMat h K θ‖ ≤ ℓ := by
    have : linMat h' K θ - linMat h K θ = sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h') (K θ) -
        fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)) := (PerturbationAux.sqMat_sub _ _).symm
    rw [this, norm_sqMat]
    exact hDX
  rw [torsion_sub_param h h' K ω hN]
  calc _ ≤ ‖(normalMat K θ)ᵀ * omegaZeroMatrix n‖ *
        ‖(linMat h' K θ - linMat h K θ) * normalMat K θ‖ := Matrix.linfty_opNorm_mul _ _
    _ = ‖(normalMat K θ)ᵀ‖ * ‖(linMat h' K θ - linMat h K θ) * normalMat K θ‖ := by
        rw [norm_mul_omegaZeroMatrix]
    _ ≤ (2 * n * (a * b)) * (ℓ * (a * b)) := by
        refine mul_le_mul ((FrameAux.norm_transpose_le_two_mul _).trans ?_)
          ((Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hΔ hNb (norm_nonneg _) ?_))
          (norm_nonneg _) (by positivity)
        · gcongr
        · exact (norm_nonneg _).trans hΔ
    _ = 2 * n * (a * b) ^ 2 * ℓ := by ring

/-- The averaged torsions of `h'` and `h` on the same torus differ by at most `A` if their
(continuous) tori do. -/
theorem norm_torsionAverage_sub_param_le (h h' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {A : ℝ}
    (hc : Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))))
    (hc' : Continuous (fun x : Fin n → ℝ => torsion h' K ω (fun i => (x i : ℂ))))
    (hb : ∀ x : Fin n → ℝ, ‖torsion h' K ω (fun i => (x i : ℂ)) -
      torsion h K ω (fun i => (x i : ℂ))‖ ≤ A) :
    ‖torsionAverage h' K ω - torsionAverage h K ω‖ ≤ A := by
  rw [torsionAverage_eq_avg h K ω hc, torsionAverage_eq_avg h' K ω hc']
  have heq : avg (torsion h' K ω) - avg (torsion h K ω) = torusAverage (fun x : Fin n → ℝ =>
      torsion h' K ω (fun i => (x i : ℂ)) - torsion h K ω (fun i => (x i : ℂ))) := by
    unfold avg torusAverage
    rw [integral_sub (integrableOn_unitCube_of_continuous hc')
      (integrableOn_unitCube_of_continuous hc)]
  rw [heq]
  exact norm_torusAverage_le fun x _ => hb x

/-- Quantitative Neumann step in row-sum form: if `T₀` is invertible with row sums of `T₀⁻¹` at most
`b`, `‖T - T₀‖ ≤ Δ`, `b Δ ≤ 1/2` and `b ≤ B (1 - b Δ)`, then `T` is invertible with row sums of
  `T⁻¹` at
most `B`. Index-generic (used for `Fin n` and for the bordered `Fin n ⊕ Unit`). -/
theorem inv_rowSum_of_perturb {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {T₀ T : Matrix ι ι ℂ} {b Δ B : ℝ}
    (hU : IsUnit T₀.det) (hb : ∀ i, ∑ j, ‖T₀⁻¹ i j‖ ≤ b) (hΔ : ‖T - T₀‖ ≤ Δ)
    (hbΔ : b * Δ ≤ 1 / 2) (hB : b ≤ B * (1 - b * Δ)) :
    IsUnit T.det ∧ ∀ i, ∑ j, ‖T⁻¹ i j‖ ≤ B := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hb0 : 0 ≤ b := (Finset.sum_nonneg fun j _ => norm_nonneg (T₀⁻¹ i₀ j)).trans (hb i₀)
  have hinv : ‖T₀⁻¹‖ ≤ b := (norm_le_iff_forall_rowSum hb0).2 hb
  have hΔ0 : 0 ≤ Δ := (norm_nonneg _).trans hΔ
  have hsmall : ‖T₀⁻¹‖ * ‖T - T₀‖ ≤ 1 / 2 :=
    (mul_le_mul hinv hΔ (norm_nonneg _) hb0).trans hbΔ
  obtain ⟨hTu, -, -⟩ := neumann (Matrix.isUnit_iff_isUnit_det _ |>.2 hU) (Δ := T - T₀)
    (by simpa using hsmall)
  rw [add_sub_cancel] at hTu
  have hTd : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).1 hTu
  refine ⟨hTd, fun i => (rowSum_le_norm _ i).trans ?_⟩
  have hid : T⁻¹ = T₀⁻¹ - T₀⁻¹ * (T - T₀) * T⁻¹ := by
    have h1 : T₀⁻¹ * (T - T₀) * T⁻¹ = T₀⁻¹ - T⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd,
        Matrix.mul_one, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    rw [h1]; abel
  have hle : ‖T⁻¹‖ ≤ b + (b * Δ) * ‖T⁻¹‖ := by
    calc ‖T⁻¹‖ = ‖T₀⁻¹ - T₀⁻¹ * (T - T₀) * T⁻¹‖ := congrArg norm hid
      _ ≤ ‖T₀⁻¹‖ + ‖T₀⁻¹ * (T - T₀) * T⁻¹‖ := norm_sub_le _ _
      _ ≤ b + (b * Δ) * ‖T⁻¹‖ := by
        refine add_le_add hinv ((Matrix.linfty_opNorm_mul _ _).trans ?_)
        exact mul_le_mul_of_nonneg_right
          ((Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hinv hΔ (norm_nonneg _) hb0))
          (norm_nonneg _)
  have hpos : 0 < 1 - b * Δ := by linarith
  have hB0 : 0 ≤ B := by
    by_contra hneg
    push Not at hneg
    nlinarith
  nlinarith [norm_nonneg T⁻¹]

end KAM.Sharp

end
