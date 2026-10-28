/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.CutoffTensor

/-! # P11B smooth cutoff: the scaled tensor kernel

The rescaled bump `x ↦ δ⁻¹ * ψ (δ⁻¹ * x)` and the tensor kernel `w ↦ ∏ j, ψ_δ (w j)`: support in
the sup-norm ball of radius `δ`, unit integral, and the exact `L¹` norm of every coordinate
derivative of order `k ≤ μ`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- The bump rescaled to the interval `[-δ, δ]`. -/
def selectionBumpScaled (μ : ℕ) (δ x : ℝ) : ℝ := δ⁻¹ * selectionBump μ (δ⁻¹ * x)

/-- The tensor kernel of the cutoff. -/
def selectionKernel (n μ : ℕ) (δ : ℝ) (w : Fin n → ℝ) : ℝ := ∏ j, selectionBumpScaled μ δ (w j)

theorem selectionMult_sum {k : ℕ} (i : Fin k → Fin n) : ∑ j, selectionMult i j = k := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset (Fin n))) (f := i) (fun _ _ => Finset.mem_univ _)
  simpa [selectionMult] using this.symm

theorem selectionBumpScaled_contDiff (μ : ℕ) {δ : ℝ} :
    ContDiff ℝ μ (selectionBumpScaled μ δ) :=
  contDiff_const.mul ((selectionBump_contDiff μ).comp (contDiff_const.mul contDiff_id))

theorem selectionBumpScaled_iteratedDeriv (μ : ℕ) {δ : ℝ} {m : ℕ} (hm : m ≤ μ) :
    iteratedDeriv m (selectionBumpScaled μ δ) =
      fun x => δ⁻¹ * (δ⁻¹ ^ m * iteratedDeriv m (selectionBump μ) (δ⁻¹ * x)) := by
  have h : ContDiff ℝ (m : ℕ) (selectionBump μ) :=
    (selectionBump_contDiff μ).of_le (by exact_mod_cast hm)
  funext x
  have e : selectionBumpScaled μ δ = fun x => δ⁻¹ * (fun x => selectionBump μ (δ⁻¹ * x)) x := rfl
  rw [e, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul h]

theorem selectionBumpScaled_nonneg (μ : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ selectionBumpScaled μ δ x :=
  mul_nonneg (inv_nonneg.2 hδ.le) (selectionBump_nonneg μ _)

theorem selectionBumpScaled_eq_zero (μ : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hx : δ < |x|) :
    selectionBumpScaled μ δ x = 0 := by
  have : 1 ≤ |δ⁻¹ * x| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hδ), ← div_eq_inv_mul, le_div_iff₀ hδ]
    linarith
  have h0 : selectionBump μ (δ⁻¹ * x) = 0 := by
    simp [selectionBump, selectionBumpRaw_eq_zero μ this]
  simp [selectionBumpScaled, h0]

theorem selectionBumpScaled_integral (μ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x : ℝ, selectionBumpScaled μ δ x = 1 := by
  unfold selectionBumpScaled
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => selectionBump μ x) δ⁻¹,
    selectionBump_integral, inv_inv, abs_of_pos hδ]
  simp [hδ.ne']

theorem selectionBumpScaled_L1 (μ : ℕ) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : m ≤ μ) :
    ∫ x : ℝ, |iteratedDeriv m (selectionBumpScaled μ δ) x| =
      δ⁻¹ ^ m * selectionBumpL1 μ m := by
  rw [selectionBumpScaled_iteratedDeriv μ hm]
  have : ∀ x : ℝ, |δ⁻¹ * (δ⁻¹ ^ m * iteratedDeriv m (selectionBump μ) (δ⁻¹ * x))| =
      (δ⁻¹ ^ (m + 1)) * (fun y => |iteratedDeriv m (selectionBump μ) y|) (δ⁻¹ * x) := by
    intro x
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hδ), abs_of_nonneg (pow_nonneg (inv_nonneg.2 hδ.le) _),
      pow_succ]
    ring
  simp_rw [this]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun y => |iteratedDeriv m (selectionBump μ) y|) δ⁻¹, inv_inv, abs_of_pos hδ]
  unfold selectionBumpL1
  simp only [smul_eq_mul]
  have h : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ.ne'
  rw [pow_succ]
  linear_combination (δ⁻¹ ^ m * ∫ y : ℝ, |iteratedDeriv m (selectionBump μ) y|) * h

theorem selectionKernel_contDiff (n μ : ℕ) {δ : ℝ} : ContDiff ℝ μ (selectionKernel n μ δ) :=
  contDiff_prod fun j _ => (selectionBumpScaled_contDiff μ).comp (contDiff_pi.1 contDiff_id j)

theorem selectionKernel_nonneg (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) (w : Fin n → ℝ) :
    0 ≤ selectionKernel n μ δ w :=
  Finset.prod_nonneg fun j _ => selectionBumpScaled_nonneg μ hδ _

theorem selectionKernel_ne_zero (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) {w : Fin n → ℝ}
    (hw : selectionKernel n μ δ w ≠ 0) : ‖w‖ ≤ δ := by
  refine (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_
  by_contra h
  rw [Real.norm_eq_abs, not_le] at h
  exact hw (Finset.prod_eq_zero (Finset.mem_univ j) (selectionBumpScaled_eq_zero μ hδ h))

theorem selectionKernel_hasCompactSupport (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (selectionKernel n μ δ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℝ) δ) ?_
  intro w hw
  simpa using selectionKernel_ne_zero n μ hδ hw

theorem selectionKernel_integral (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w : Fin n → ℝ, selectionKernel n μ δ w = 1 := by
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (ι := Fin n) (E := fun _ => ℝ)
    (μ := fun _ => (volume : Measure ℝ)) fun _ => selectionBumpScaled μ δ
  simp only [selectionBumpScaled_integral μ hδ, Finset.prod_const_one] at this
  exact this

theorem selectionKernel_coord_L1 (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : k ≤ μ)
    (i : Fin k → Fin n) :
    ∫ w : Fin n → ℝ, |iteratedFDeriv ℝ k (selectionKernel n μ δ) w (fun l => Pi.single (i l) 1)| =
      δ⁻¹ ^ k * ∏ j, selectionBumpL1 μ (selectionMult i j) := by
  have hf : ∀ j : Fin n, ContDiff ℝ (k : ℕ) (selectionBumpScaled μ δ) := fun _ =>
    (selectionBumpScaled_contDiff μ).of_le (by exact_mod_cast hk)
  have hmult : ∀ j, selectionMult i j ≤ μ := fun j => by
    have : selectionMult i j ≤ ∑ j, selectionMult i j :=
      Finset.single_le_sum (f := fun j => selectionMult i j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    rw [selectionMult_sum] at this
    omega
  have h1 : ∀ w, iteratedFDeriv ℝ k (selectionKernel n μ δ) w (fun l => Pi.single (i l) 1) =
      ∏ j, iteratedDeriv (selectionMult i j) (selectionBumpScaled μ δ) (w j) := fun w =>
    selectionTensor_iteratedFDeriv (fun _ => selectionBumpScaled μ δ) k hf i w
  simp_rw [h1, Finset.abs_prod]
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (ι := Fin n) (E := fun _ => ℝ)
    (μ := fun _ => (volume : Measure ℝ))
    fun j => fun x => |iteratedDeriv (selectionMult i j) (selectionBumpScaled μ δ) x|
  refine (this.trans ?_)
  rw [Finset.prod_congr rfl fun j _ => selectionBumpScaled_L1 μ hδ (hmult j)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, selectionMult_sum]

end KAM.Planetary
