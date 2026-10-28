/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Diag
public import KAM.Planetary.PlanarTorsion.NormalForm.Remainder
public import KAM.Planetary.PlanarTorsion.Frame

/-!
# Planar quartic torsion: diagonal derivatives at the origin (package T16)

Helper lemmas for `stepP:p11b:bt-K`: the diagonal derivative `iteratedFDeriv ℝ j f 0 (fun _ => z)`
of a function analytic at `0` is the `j`-th derivative at `0` of `t ↦ f (t • z)`; it is natural
for linear changes of variable (`p11cB_rotCLM`) and it vanishes in odd order for even functions.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

/-- The diagonal derivative is the one-variable derivative along the ray. -/
theorem p11cB_diag {f : Phase 2 → ℝ} (hf : AnalyticAt ℝ f 0) (j : ℕ) (z : Phase 2) :
    iteratedFDeriv ℝ j f 0 (fun _ => z) = iteratedDeriv j (fun t : ℝ => f (t • z)) 0 := by
  have hV : IsOpen {w | AnalyticAt ℝ f w} := isOpen_analyticAt ℝ f
  have hcd : ContDiffOn ℝ j f {w | AnalyticAt ℝ f w} := fun w hw =>
    (hw.contDiffAt (n := j)).contDiffWithinAt
  have h := p11cN_iteratedFDeriv_line hV j hcd 0 z (t := 0) (by simpa using hf)
  have h2 := congrArg (fun L => L (fun _ : Fin j => (1 : ℝ))) h
  simp only [zero_add, zero_smul, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at h2
  rw [iteratedDeriv_eq_iteratedFDeriv, h2]

/-- The rotation of the slow variables as a continuous linear map. -/
def p11cB_rotCLM (U : Matrix (Fin 2) (Fin 2) ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (((Matrix.toLin' U).toContinuousLinearMap).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).prod
    (((Matrix.toLin' U).toContinuousLinearMap).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)))

theorem p11cB_rotCLM_apply (U : Matrix (Fin 2) (Fin 2) ℝ) (z : Phase 2) :
    p11cB_rotCLM U z = p11c_rotateSlow U z := by
  simp [p11cB_rotCLM, p11c_rotateSlow, Matrix.toLin'_apply]

/-- Diagonal derivatives are natural for linear changes of variable. -/
theorem p11cB_diag_comp {f : Phase 2 → ℝ} (hf : AnalyticAt ℝ f 0) (U : Matrix (Fin 2) (Fin 2) ℝ)
    (j : ℕ) (z : Phase 2) :
    iteratedFDeriv ℝ j (fun w => f (p11c_rotateSlow U w)) 0 (fun _ => z) =
      iteratedFDeriv ℝ j f 0 (fun _ => p11c_rotateSlow U z) := by
  have hL : ∀ w, p11c_rotateSlow U w = p11cB_rotCLM U w := fun w =>
    (p11cB_rotCLM_apply U w).symm
  have hfa : AnalyticAt ℝ (fun w => f (p11c_rotateSlow U w)) 0 := by
    have : (fun w => f (p11c_rotateSlow U w)) = f ∘ (p11cB_rotCLM U) := by
      funext w; simp [hL]
    rw [this]
    exact hf.comp_of_eq ((p11cB_rotCLM U).analyticAt 0) (map_zero _)
  rw [p11cB_diag hfa, p11cB_diag hf]
  congr 1
  funext t
  simp only [hL, map_smul]

/-- Odd diagonal derivatives of an even function vanish. -/
theorem p11cB_diag_odd {f : Phase 2 → ℝ} (hf : AnalyticAt ℝ f 0)
    (hev : ∀ᶠ w in 𝓝 (0 : Phase 2), f (-w) = f w) {j : ℕ} (hj : Odd j) (z : Phase 2) :
    iteratedFDeriv ℝ j f 0 (fun _ => z) = 0 := by
  rw [p11cB_diag hf]
  set g : ℝ → ℝ := fun t => f (t • z) with hg
  have hgev : (fun t : ℝ => g (-t)) =ᶠ[𝓝 0] g := by
    have hc : Continuous fun t : ℝ => t • z := continuous_id.smul continuous_const
    have h0 : Tendsto (fun t : ℝ => t • z) (𝓝 0) (𝓝 (0 : Phase 2)) := by
      simpa using hc.tendsto 0
    filter_upwards [h0.eventually hev] with t ht
    simp only [hg, neg_smul] at ht ⊢
    exact ht
  have h1 := iteratedDeriv_comp_neg j g 0
  rw [neg_zero, hgev.iteratedDeriv_eq] at h1
  rw [hj.neg_one_pow] at h1
  simp at h1
  linarith

/-- Diagonal derivatives of a constant plus homogeneous quadratic plus homogeneous quartic. -/
theorem p11cB_iteratedDeriv_poly (c a b : ℝ) (j : ℕ) (hj : j ≤ 5) :
    iteratedDeriv j (fun t : ℝ => c + a * t ^ 2 + b * t ^ 4) 0 =
      if j = 0 then c else if j = 2 then 2 * a else if j = 4 then 24 * b else 0 := by
  have h1 : deriv (fun t : ℝ => c + a * t ^ 2 + b * t ^ 4) =
      fun t => 2 * a * t + 4 * b * t ^ 3 := by
    funext t
    have h : HasDerivAt (fun t : ℝ => c + a * t ^ 2 + b * t ^ 4) (2 * a * t + 4 * b * t ^ 3) t := by
      have := (((hasDerivAt_const t c).add ((hasDerivAt_pow 2 t).const_mul a)).add
        ((hasDerivAt_pow 4 t).const_mul b))
      refine this.congr_deriv ?_
      simp; ring
    exact h.deriv
  have h2 : deriv (fun t : ℝ => 2 * a * t + 4 * b * t ^ 3) =
      fun t => 2 * a + 12 * b * t ^ 2 := by
    funext t
    have h : HasDerivAt (fun t : ℝ => 2 * a * t + 4 * b * t ^ 3) (2 * a + 12 * b * t ^ 2) t := by
      have := (((hasDerivAt_id t).const_mul (2 * a)).add ((hasDerivAt_pow 3 t).const_mul (4 * b)))
      refine this.congr_deriv ?_
      simp; ring
    exact h.deriv
  have h3 : deriv (fun t : ℝ => 2 * a + 12 * b * t ^ 2) = fun t => 24 * b * t := by
    funext t
    have h : HasDerivAt (fun t : ℝ => 2 * a + 12 * b * t ^ 2) (24 * b * t) t := by
      have := ((hasDerivAt_const t (2 * a)).add ((hasDerivAt_pow 2 t).const_mul (12 * b)))
      refine this.congr_deriv ?_
      simp; ring
    exact h.deriv
  have h4 : deriv (fun t : ℝ => 24 * b * t) = fun _ => 24 * b := by
    funext t
    simp
  have h5 : deriv (fun _ : ℝ => 24 * b) = fun _ => 0 := by
    funext t; simp
  interval_cases j
  · simp
  · rw [iteratedDeriv_one, h1]; simp
  · rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]; simp
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h1, h2, h3]; simp
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h1, h2, h3,
      h4]; simp
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, h1, h2, h3, h4, h5]; simp

end KAM.Planetary

end
