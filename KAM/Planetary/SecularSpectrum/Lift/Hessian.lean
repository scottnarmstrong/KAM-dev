/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Lift.Calculus

/-!
# Secular spectrum: the entrywise second derivative of a rotation family

Blueprint P, Part 9 (`stepP:p9:lift-anti`): the matrix `hess R I x y` of second derivatives of
the entries of `R`, its linear dependence on `y`, its symmetry in `(x, y)` for analytic `R`
(commuting second derivatives), and the line derivative of `I ↦ fderiv R I y`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Hessian

/-- A continuous linear map on `Vec n` is determined by its values on the standard basis. -/
lemma clm_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Vec n →L[ℝ] F) (x : Vec n) : L x = ∑ l, x l • L (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- Entrywise second derivative of a matrix-valued function. -/
def hess (R : Vec n → Mat n) (I x y : Vec n) : Mat n :=
  fun a b => fderiv ℝ (fderiv ℝ (fun J => R J a b)) I x y

lemma hess_eq_sum (R : Vec n → Mat n) (I x y : Vec n) :
    hess R I x y = ∑ l, y l • hess R I x (Pi.single l 1) := by
  funext a b
  simp only [hess, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact clm_apply_eq_sum (fderiv ℝ (fderiv ℝ (fun J => R J a b)) I x) y

lemma fderiv_eq_sum (R : Vec n → Mat n) (I y : Vec n) :
    fderiv ℝ R I y = ∑ l, y l • fderiv ℝ R I (Pi.single l 1) :=
  clm_apply_eq_sum (fderiv ℝ R I) y

lemma hess_symm {W : Set (Vec n)} {R : Vec n → Mat n} (hAn : AnalyticOnNhd ℝ R W) {I : Vec n}
    (hI : I ∈ W) (x y : Vec n) : hess R I x y = hess R I y x := by
  funext a b
  exact (analyticAt_matrix_entry (hAn I hI) a b).contDiffAt.isSymmSndFDerivAt_of_omega x y

/-- Line derivative of `fderiv R` in a direction `x`, applied to `y`. -/
lemma hasDerivAt_fderiv_line {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) {I : Vec n} (hI : I ∈ W) (x y : Vec n) :
    HasDerivAt (fun s : ℝ => fderiv ℝ R (I + s • x) y) (hess R I x y) 0 := by
  refine hasDerivAt_mat fun a b => ?_
  have hc : Continuous fun s : ℝ => I + s • x := by fun_prop
  have hnb : (fun s : ℝ => I + s • x) ⁻¹' W ∈ 𝓝 (0:ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hI)
  have hr : AnalyticAt ℝ (fun J => R J a b) I := analyticAt_matrix_entry (hAn I hI) a b
  have h1 : HasFDerivAt (fderiv ℝ (fun J => R J a b))
      (fderiv ℝ (fderiv ℝ (fun J => R J a b)) I) I :=
    (hr.fderiv.differentiableAt).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ (fun J => R J a b)) (fderiv ℝ (fderiv ℝ (fun J => R J a b)) I)
      (I + (0:ℝ) • x) := by simpa using h1
  have h3 := h2.comp_hasDerivAt (0:ℝ) (hasDerivAt_line I x 0)
  have h4 := (ContinuousLinearMap.apply ℝ ℝ y).hasFDerivAt.comp_hasDerivAt (0:ℝ) h3
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [hnb] with s hs
  exact fderiv_entry (hAn _ hs).differentiableAt y a b

end Hessian

end SecularSpectrum

end KAM.Planetary

end
