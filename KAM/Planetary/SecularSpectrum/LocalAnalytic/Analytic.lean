/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Frame

/-!
# Secular spectrum: analyticity of the eigenprojections and the eigenframe

Blueprint P, Part 9 (`stepP:p9:la-adj`, `stepP:p9:la-vec`).  The eigenprojection `Π_j` of an
analytic symmetric family with analytic, pointwise distinct nodes `σ` is analytic, being a finite
product of the analytic matrices `(σ j - σ k)⁻¹ (M - σ k)`; with positive diagonal entries the
normalised columns of `eigFrame` are analytic as well.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Analytic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E}

lemma analyticAt_mat_entry {F : E → Mat n} (h : AnalyticAt ℝ F w) (a b : Fin n) :
    AnalyticAt ℝ (fun y => F y a b) w :=
  analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h a) b

lemma analyticAt_mat_mul {F G : E → Mat n} (hF : AnalyticAt ℝ F w) (hG : AnalyticAt ℝ G w) :
    AnalyticAt ℝ (fun x => F x * G x) w := by
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun l _ =>
    (analyticAt_mat_entry hF i l).mul (analyticAt_mat_entry hG l j)

lemma analyticAt_list_prod (A : Fin n → E → Mat n) (hA : ∀ k, AnalyticAt ℝ (A k) w)
    (l : List (Fin n)) : AnalyticAt ℝ (fun x => (l.map fun k => A k x).prod) w := by
  induction l with
  | nil => simpa using analyticAt_const
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact analyticAt_mat_mul (hA a) ih

lemma eigProj_eq_list (M : Mat n) (σ : Vec n) (j : Fin n) :
    eigProj M σ j = (((Finset.univ.erase j).toList).map
      fun k => (σ j - σ k)⁻¹ • (M - σ k • (1 : Mat n))).prod := by
  unfold eigProj Lagrange.basis
  rw [← Finset.prod_map_toList, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp [Lagrange.basisDivisor, Algebra.algebraMap_eq_smul_one, smul_sub]

lemma analyticAt_eigProj {M : E → Mat n} {σ : E → Vec n} (hM : AnalyticAt ℝ M w)
    (hσ : ∀ k, AnalyticAt ℝ (fun x => σ x k) w) (hinj : Function.Injective (σ w)) (j : Fin n) :
    AnalyticAt ℝ (fun x => eigProj (M x) (σ x) j) w := by
  simp_rw [eigProj_eq_list]
  refine analyticAt_list_prod (fun k x => (σ x j - σ x k)⁻¹ • (M x - σ x k • (1 : Mat n)))
    (fun k => ?_) _
  by_cases hk : k = j
  · subst hk
    simp only [sub_self, inv_zero, zero_smul]
    exact analyticAt_const
  · refine AnalyticAt.smul (((hσ j).sub (hσ k)).inv ?_) (hM.sub ((hσ k).smul analyticAt_const))
    exact sub_ne_zero.2 fun h => hk (hinj h).symm

lemma analyticAt_eigFrame {M : E → Mat n} {σ : E → Vec n} {k : Fin n → Fin n}
    (hM : AnalyticAt ℝ M w) (hσ : ∀ i, AnalyticAt ℝ (fun x => σ x i) w)
    (hinj : Function.Injective (σ w)) (hpos : ∀ j, 0 < eigProj (M w) (σ w) j (k j) (k j)) :
    AnalyticAt ℝ (fun x => eigFrame (M x) (σ x) k) w := by
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  simp only [eigFrame, Matrix.of_apply]
  have hP := analyticAt_eigProj hM hσ hinj j
  refine (analyticAt_mat_entry hP i (k j)).div ?_ (Real.sqrt_pos.2 (hpos j)).ne'
  exact (analyticAt_mat_entry hP (k j) (k j)).contDiffAt.sqrt (hpos j).ne' |>.analyticAt

end Analytic

end SecularSpectrum

end KAM.Planetary
