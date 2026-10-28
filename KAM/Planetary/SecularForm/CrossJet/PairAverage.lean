/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.CrossJet.PairIntegrand
public import KAM.Planetary.SecularForm.CrossJet.MixedKernel
public import KAM.Planetary.SecularForm.Basic

/-!
# Cross jet: the mixed second derivative of the literal pair average

Blueprint P, Part 8, `stepP:p8:qf-cross` (with `bpP:p8:e-diff`): for two planets with separated axes the
mixed second derivative at `ξ₁ = ξ₂ = 0` of the literal pair average `pairSlowSecular` is the
double average over `(λ₁, λ₂)` of `crossKernel` evaluated at the circular positions and the first
orbit variations (`hasDerivAt_poincare_fst_xi`). No Laplace series is used here; the Fourier
selection is the next module.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary
namespace SecularForm
variable {n : ℕ}

theorem poincare_circle_fst {m κ Λ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hΛ : 0 < Λ) (l : ℝ) :
    (poincare m κ (![l, 0], ![Λ, 0])).1 =
      (Λ ^ 2 / (m ^ 2 * κ)) • (![Real.cos l, Real.sin l] : Fin 2 → ℝ) := by
  rw [poincare_circular hm hκ hΛ]

theorem circle_sub_ne {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h : a₁ < a₂) (x y : ℝ) :
    a₁ • (![Real.cos x, Real.sin x] : Fin 2 → ℝ) - a₂ • (![Real.cos y, Real.sin y] : Fin 2 → ℝ)
      ≠ 0 := by
  intro h0
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  simp at e0 e1
  have : a₁ ^ 2 = a₂ ^ 2 := by
    linear_combination (a₁ * Real.cos x + a₂ * Real.cos y) * e0 +
      (a₁ * Real.sin x + a₂ * Real.sin y) * e1 - a₁ ^ 2 * Real.cos_sq_add_sin_sq x +
      a₂ ^ 2 * Real.cos_sq_add_sin_sq y
  nlinarith

theorem slice_mem_pairDom {m₁ m₂ κ I₁ I₂ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hκ : 0 < κ)
    (hI₁ : 0 < I₁) (hI₂ : 0 < I₂) (hsep : I₁ ^ 2 / (m₁ ^ 2 * κ) < I₂ ^ 2 / (m₂ ^ 2 * κ))
    (t : Vec 2) : (t, (0 : Vec 2)) ∈ pairDom m₁ m₂ κ I₁ I₂ := by
  refine ⟨⟨hI₁, ?_⟩, ⟨hI₂, ?_⟩, ?_⟩
  · simpa [sliceBlock, poincareGamma] using hI₁
  · simpa [sliceBlock, poincareGamma] using hI₂
  · have h1 : sliceBlock I₁ 0 (t, 0) = (![t 0, 0], ![I₁, 0]) := by simp [sliceBlock]
    have h2 : sliceBlock I₂ 1 (t, 0) = (![t 1, 0], ![I₂, 0]) := by simp [sliceBlock]
    rw [h1, h2, poincare_circle_fst hm₁ hκ hI₁, poincare_circle_fst hm₂ hκ hI₂]
    exact circle_sub_ne (by positivity) hsep _ _

theorem crossKernel_const_mul (k c : ℝ) (d x z : Fin 2 → ℝ) :
    crossKernel (k * c) d x z = k * crossKernel c d x z := by
  unfold crossKernel; ring

/-- First variation vector `(-1 - sin² λ, sin λ cos λ)`. -/
def uvec (l : ℝ) : Fin 2 → ℝ := ![-1 - Real.sin l ^ 2, Real.sin l * Real.cos l]
/-- Unit vector `(cos λ, sin λ)`. -/
def cvec (l : ℝ) : Fin 2 → ℝ := ![Real.cos l, Real.sin l]

theorem pairSlowSecular_mixed_jet (D : Data n) (i j : Fin n) {I J : ℝ} (hI : 0 < I) (hJ : 0 < J)
    (hsep : I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    iteratedFDeriv ℝ 2 (fun y : Vec 2 => pairSlowSecular D i j I J (![y 0, 0], ![y 1, 0])) 0
        ![Pi.single 0 1, Pi.single 1 1] =
      (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π,
        crossKernel (D.G * D.m i * D.m j)
          ((I ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) • cvec s -
            (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) • cvec t)
          (((I ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) / √I) • uvec s)
          (((J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) / √J) • uvec t) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  set κ := D.G * D.m0 with hκdef
  set c := D.G * D.m i * D.m j with hc
  set k : ℝ := (2 * π)⁻¹ * (2 * π)⁻¹ with hk
  set F : Vec 2 × Vec 2 → ℝ := fun p => k * pairIntegrand c (D.m i) (D.m j) κ I J p with hF
  have hW := isOpen_pairDom (m₁ := D.m i) (m₂ := D.m j) (I₁ := I) (I₂ := J) (D.hm i) (D.hm j) hκ
  have hFd : ContDiffOn ℝ 2 F (pairDom (D.m i) (D.m j) κ I J) :=
    contDiffOn_const.mul ((contDiffOn_pairIntegrand (c := c) (I₁ := I) (I₂ := J) (D.hm i) (D.hm j) hκ).of_le
      (by exact_mod_cast le_top))
  obtain ⟨δ, hδ, hmem, hcont, heq⟩ := e_diff_slice hW hFd
    (fun t _ => slice_mem_pairDom (D.hm i) (D.hm j) hκ hI hJ hsep t)
  have hslice : ∀ y ∈ ball (0 : Vec 2) δ, ContinuousOn (fun t => F (t, y)) (cell 2) := by
    intro y hy
    exact hFd.continuousOn.comp (by fun_prop : Continuous fun t : Vec 2 => (t, y)).continuousOn
      (fun t ht => hmem t ht y hy)
  have h2π : (0:ℝ) ≤ 2 * π := by positivity
  have hfun : ∀ y ∈ ball (0 : Vec 2) δ,
      pairSlowSecular D i j I J (![y 0, 0], ![y 1, 0]) = ∫ t in cell 2, F (t, y) := by
    intro y hy
    rw [integral_cell_two (hslice y hy)]
    unfold pairSlowSecular
    simp only [hF, pairIntegrand, sliceBlock, intervalIntegral.integral_const_mul]
    have hneg : -D.G * D.m i * D.m j = -c := by rw [hc]; ring
    simp only [hneg, Matrix.cons_val_zero, Matrix.cons_val_one, hk]
    ring
  have hEq : (fun y : Vec 2 => pairSlowSecular D i j I J (![y 0, 0], ![y 1, 0])) =ᶠ[𝓝 0]
      fun y => ∫ t in cell 2, F (t, y) :=
    Filter.eventually_of_mem (ball_mem_nhds 0 hδ) hfun
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hEq 2).self_of_nhds, heq]
  set m : Fin 2 → Vec 2 := ![Pi.single 0 1, Pi.single 1 1] with hm
  have hcm : ContinuousOn (fun t => iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0 m) (cell 2) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Vec 2) ℝ m).continuous.comp_continuousOn
      hcont
  have hint : IntegrableOn (fun t => iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0) (cell 2) :=
    hcont.integrableOn_compact isCompact_cell
  have happ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Vec 2) ℝ m).integral_comp_comm
    hint
  have hcomm : (∫ t in cell 2, iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0) m =
      ∫ t in cell 2, iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0 m := by
    simpa using happ.symm
  rw [hcomm]
  set a₁ := I ^ 2 / (D.m i ^ 2 * κ) with ha₁
  set a₂ := J ^ 2 / (D.m j ^ 2 * κ) with ha₂
  have hpt : ∀ t ∈ cell 2, iteratedFDeriv ℝ 2 (fun y => F (t, y)) 0 m =
      k * crossKernel c (a₁ • cvec (t 0) - a₂ • cvec (t 1))
        ((a₁ / √I) • uvec (t 0)) ((a₂ / √J) • uvec (t 1)) := by
    intro t ht
    have hα : HasDerivAt (fun s => (poincare (D.m i) κ (![t 0, s], ![I, 0])).1)
        ((a₁ / √I) • uvec (t 0)) 0 := by
      have := hasDerivAt_poincare_fst_xi (m := D.m i) (κ := κ) hI (t 0)
      simpa [ha₁, uvec] using this
    have hβ : HasDerivAt (fun s => (poincare (D.m j) κ (![t 1, s], ![J, 0])).1)
        ((a₂ / √J) • uvec (t 1)) 0 := by
      have := hasDerivAt_poincare_fst_xi (m := D.m j) (κ := κ) hJ (t 1)
      simpa [ha₂, uvec] using this
    have hne : (poincare (D.m i) κ (![t 0, 0], ![I, 0])).1 -
        (poincare (D.m j) κ (![t 1, 0], ![J, 0])).1 ≠ 0 := by
      rw [poincare_circle_fst (D.hm i) hκ hI, poincare_circle_fst (D.hm j) hκ hJ]
      exact circle_sub_ne (div_pos (pow_pos hI 2) (mul_pos (pow_pos (D.hm i) 2) hκ)) hsep _ _
    have hC : ContDiffAt ℝ 2 (fun y => F (t, y)) 0 :=
      (hFd.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun y hy => hmem t ht y hy)).contDiffAt (ball_mem_nhds 0 hδ)
    have key := iteratedFDeriv_two_mixed (k * c) hα hβ hne (f := fun y => F (t, y))
      (by intro y; simp only [hF, pairIntegrand, sliceBlock]; ring) hC
    rw [hm, key, crossKernel_const_mul, poincare_circle_fst (D.hm i) hκ hI,
      poincare_circle_fst (D.hm j) hκ hJ]
    rfl
  rw [setIntegral_congr_fun measurableSet_cell hpt,
    integral_cell_two (hcm.congr (fun t ht => (hpt t ht).symm))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, intervalIntegral.integral_const_mul, hk]
  ring

end SecularForm
end KAM.Planetary
