/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Lift.Analytic

/-!
# Secular spectrum: line-derivative calculus for the lift

Blueprint P, Part 9 (`stepP:p9:lift-anti`): coordinatewise derivative rules for matrix and vector
valued functions of one real variable, the derivative of an orthogonal family
(`R Rᵀ = 1` differentiates to `(∂R) Rᵀ + R (∂R)ᵀ = 0`), and symmetry of the scalar second
derivative of an analytic function.  Matrix-valued second derivatives are handled entrywise,
since `fderiv ℝ (fderiv ℝ R)` has no norm instance on `Mat n` with the elementwise norm.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Calculus

lemma hasDerivAt_mat {A : ℝ → Mat n} {A' : Mat n} {t : ℝ}
    (h : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t) : HasDerivAt A A' t :=
  hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b

lemma hasDerivAt_mat_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : HasDerivAt A A' t)
    (a b : Fin n) : HasDerivAt (fun s => A s a b) (A' a b) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b

lemma hasDerivAt_vec_entry {x : ℝ → Vec n} {x' : Vec n} {t : ℝ} (h : HasDerivAt x x' t)
    (a : Fin n) : HasDerivAt (fun s => x s a) (x' a) t :=
  hasDerivAt_pi.1 h a

lemma hasDerivAt_mat_transpose {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).transpose) A'.transpose t :=
  hasDerivAt_mat fun a b => hasDerivAt_mat_entry h b a

lemma hasDerivAt_mat_mul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  refine hasDerivAt_mat fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ =>
    (hasDerivAt_mat_entry hA a k).fun_mul (hasDerivAt_mat_entry hB k b)

lemma hasDerivAt_mat_mulVec {M : ℝ → Mat n} {M' : Mat n} {x : ℝ → Vec n} {x' : Vec n} {t : ℝ}
    (hM : HasDerivAt M M' t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => (M s).mulVec (x s)) (M'.mulVec (x t) + (M t).mulVec x') t := by
  refine hasDerivAt_pi.2 fun a => ?_
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ =>
    (hasDerivAt_mat_entry hM a k).fun_mul (hasDerivAt_vec_entry hx k)

lemma hasDerivAt_vec_dot {x y : ℝ → Vec n} {x' y' : Vec n} {t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s) (x' ⬝ᵥ y t + x t ⬝ᵥ y') t := by
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ =>
    (hasDerivAt_vec_entry hx k).fun_mul (hasDerivAt_vec_entry hy k)

/-- The line `t ↦ I + t • v` has derivative `v`. -/
lemma hasDerivAt_line (I v : Vec n) (t : ℝ) : HasDerivAt (fun s : ℝ => I + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add I

/-- Directional derivative of a differentiable matrix function along a line. -/
lemma hasDerivAt_comp_line {R : Vec n → Mat n} {I : Vec n} (h : DifferentiableAt ℝ R I)
    (v : Vec n) : HasDerivAt (fun s : ℝ => R (I + s • v)) (fderiv ℝ R I v) 0 := by
  have h0 : HasFDerivAt R (fderiv ℝ R I) (I + (0:ℝ) • v) := by simpa using h.hasFDerivAt
  exact h0.comp_hasDerivAt (0:ℝ) (hasDerivAt_line I v 0)

/-- Differentiating `R Rᵀ = 1` along a direction. -/
lemma deriv_orth {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) {I : Vec n} (hI : I ∈ W)
    (v : Vec n) :
    fderiv ℝ R I v * (R I).transpose + R I * (fderiv ℝ R I v).transpose = 0 := by
  have h1 := hasDerivAt_comp_line (hAn I hI).differentiableAt v
  have h2 := hasDerivAt_mat_mul h1 (hasDerivAt_mat_transpose h1)
  have hev : (fun s : ℝ => R (I + s • v) * (R (I + s • v)).transpose) =ᶠ[𝓝 0] fun _ => 1 := by
    have hc : Continuous fun s : ℝ => I + s • v := by fun_prop
    have : (fun s : ℝ => I + s • v) ⁻¹' W ∈ 𝓝 (0:ℝ) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hI)
    filter_upwards [this] with s hs
    exact isSO_mul_transpose (hR _ hs)
  have h3 := h2.congr_of_eventuallyEq hev.symm
  have h4 := h3.unique (hasDerivAt_const (0:ℝ) (1 : Mat n))
  simpa using h4

/-- The other form: `(∂R)ᵀ R = - Rᵀ (∂R)`. -/
lemma deriv_orth' {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) {I : Vec n} (hI : I ∈ W)
    (v : Vec n) :
    (fderiv ℝ R I v).transpose * R I = -((R I).transpose * fderiv ℝ R I v) := by
  have h := deriv_orth hW hAn hR hI v
  have h2 := isSO_transpose_mul (hR I hI)
  have h3 : (R I).transpose * (fderiv ℝ R I v * (R I).transpose + R I *
      (fderiv ℝ R I v).transpose) * R I = 0 := by rw [h]; simp
  have e : ∀ X : Mat n, (R I).transpose * (R I * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_one, e] at h3
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h3)

lemma analyticOnNhd_transpose {W : Set (Vec n)} {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) :
    AnalyticOnNhd ℝ (fun I => (R I).transpose) W := fun I hI =>
  analyticAt_pi_iff.2 fun a => analyticAt_pi_iff.2 fun b =>
    analyticAt_matrix_entry (hAn I hI) b a

lemma isSO_transpose {R : Mat n} (h : isSO R) : isSO R.transpose :=
  ⟨by simpa using isSO_mul_transpose h, by simpa using h.2⟩

lemma fderiv_transpose {W : Set (Vec n)} {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W)
    {I : Vec n} (hI : I ∈ W) (v : Vec n) :
    fderiv ℝ (fun J => (R J).transpose) I v = (fderiv ℝ R I v).transpose := by
  funext a b
  rw [fderiv_entry (analyticOnNhd_transpose hAn I hI).differentiableAt,
    Matrix.transpose_apply, fderiv_entry (hAn I hI).differentiableAt]
  rfl

/-- On the lift domain the inverse lift is the lift of the transposed rotation. -/
lemma liftInv_eq_liftMap_transpose {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) {w : Phase (n+n)}
    (hw : w ∈ liftDomain W) : liftInv R w = liftMap (fun I => (R I).transpose) w := by
  simp only [liftInv, liftMap, Matrix.transpose_transpose]
  congr 1
  funext l
  rw [fderiv_transpose hAn hw]
  simp only [deriv_orth' hW hAn hR hw, Matrix.neg_mulVec, Pi.neg_apply,
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

end Calculus

end SecularSpectrum

end KAM.Planetary

end
