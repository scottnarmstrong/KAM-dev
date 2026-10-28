/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ParameterIntegral
public import KAM.Planetary.Poincare.Chart

/-!
# Secular form: symmetries of the chart, evenness of the secular function

Blueprint P, Part 8 (`bpP:p8:symmetries`, `bpP:p8:evenness`).  The three chart identities (S1)-(S3)
are proved one planet at a time from the uniqueness of the regular Kepler equation, then lifted to
the product chart.  The Kepler functions are invariant under the induced isometries, and the cell
average of a `2π`-periodic function is invariant under translation and reflection of the angles
(by a fundamental-domain argument that needs no integrability).  `evenness_taylor` is the
consequence for odd-order derivatives at the circular orbit.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

section PlanarSymmetries

/-- The reflection `σ = diag(1, -1)` of the plane. -/
def sigmaRefl (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![v 0, -v 1]

private theorem planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem planeDot_sigma (v w : Fin 2 → ℝ) :
    planeDot (sigmaRefl v) (sigmaRefl w) = planeDot v w := by
  simp [planeDot, Fin.sum_univ_two, sigmaRefl]

private theorem planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem gamma_mk (a x b y : ℝ) :
    poincareGamma ((![a, x] : Fin 2 → ℝ), (![b, y] : Fin 2 → ℝ)) = (x ^ 2 + y ^ 2) / 2 := by
  simp [poincareGamma]

private theorem keplerJac_eq' (v : Fin 2 → ℝ) (F : ℝ) :
    keplerJac v F = 1 - (v 0 * Real.cos F + v 1 * Real.sin F) := by
  simp [keplerJac, planeDot_two, orbitalUnit]

/-- (S1) for one planet: `(λ + π, -ξ, Λ, -η) ↦ (-q, -p)`. -/
theorem poincare_antipode {m κ : ℝ} {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ (![w.1 0 + π, -w.1 1], ![w.2 0, -w.2 1]) =
      (-(poincare m κ w).1, -(poincare m κ w).2) := by
  have hlen := (poincare_facts hw).2.2.2.2.2.1
  have hΓ : poincareGamma ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareGamma w := by
    rw [gamma_mk]; simp [poincareGamma]
  have hK : poincareK ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareK w := by
    simp only [poincareK, hΓ]; simp
  have hV : poincareV ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      -poincareV w := by
    simp only [poincareV, hΓ]; ext i; fin_cases i <;> simp
  have hF : poincareF ((![w.1 0 + π, -w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareF w + π := by
    unfold poincareF
    rw [hV]
    simp only [Matrix.cons_val_zero]
    refine keplerLong_unique (by rwa [planeLength_neg]) ?_
    have h := keplerPhi_keplerLong hlen (w.1 0)
    simp only [keplerPhi] at h ⊢
    simp only [Pi.neg_apply, Real.sin_add_pi, Real.cos_add_pi]
    linarith
  have hU : orbitalUnit (poincareF w + π) = -orbitalUnit (poincareF w) := by
    ext i; fin_cases i <;> simp [orbitalUnit]
  have hJ : keplerJac (-poincareV w) (poincareF w + π) = keplerJac (poincareV w) (poincareF w) := by
    rw [keplerJac_eq', keplerJac_eq']; simp
  have hD : planeDot (-poincareV w) (orbitalUnit (poincareF w + π)) =
      planeDot (poincareV w) (orbitalUnit (poincareF w)) := by
    rw [hU]; simp [planeDot_two]
  unfold poincare
  simp only [hK, hV, hF, hJ, hD, Matrix.cons_val_zero]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [hU, quarterTurn] <;> ring

/-- The planet block obtained by rotating the angle and `(ξ, η)` by `θ`. -/
def rotBlock (θ : ℝ) (w : Phase 2) : Phase 2 :=
  (![w.1 0 + θ, (rot θ ![w.1 1, w.2 1]) 0], ![w.2 0, (rot θ ![w.1 1, w.2 1]) 1])

private theorem planeSq_rot' (g : ℝ) (v : Fin 2 → ℝ) : planeSq (rot g v) = planeSq v := by
  have := Real.sin_sq_add_cos_sq g
  simp only [planeSq_two, rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * this

/-- (S2) for one planet: simultaneous rotation of the angle and of `(ξ, η)`. -/
theorem poincare_rotate {m κ : ℝ} (θ : ℝ) {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ (rotBlock θ w) = (rot θ (poincare m κ w).1, rot θ (poincare m κ w).2) := by
  have hlen := (poincare_facts hw).2.2.2.2.2.1
  have hΓ : poincareGamma (rotBlock θ w) = poincareGamma w := by
    have := planeSq_rot' θ ![w.1 1, w.2 1]
    simp only [poincareGamma, rotBlock, Matrix.cons_val_zero, Matrix.cons_val_one,
      planeSq_two] at this ⊢
    linarith
  have hL : (rotBlock θ w).2 0 = w.2 0 := by simp [rotBlock]
  have hK : poincareK (rotBlock θ w) = poincareK w := by
    simp only [poincareK, hΓ, hL]
  have hV : poincareV (rotBlock θ w) = rot θ (poincareV w) := by
    unfold poincareV
    rw [hΓ, hL]
    ext i; fin_cases i <;> simp [rotBlock, rot] <;> ring
  have hF : poincareF (rotBlock θ w) = poincareF w + θ := by
    have hFw : poincareF w = keplerLong (w.1 0) (poincareV w) := rfl
    show keplerLong ((rotBlock θ w).1 0) (poincareV (rotBlock θ w)) = _
    have h0 : (rotBlock θ w).1 0 = w.1 0 + θ := by simp [rotBlock]
    rw [hV, h0, hFw]
    refine keplerLong_unique (by rwa [planeLength_rot]) ?_
    have h := keplerPhi_keplerLong hlen (w.1 0)
    generalize keplerLong (w.1 0) (poincareV w) = F at h ⊢
    simp only [keplerPhi] at h ⊢
    simp only [rot, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_add, Real.cos_add]
    have := Real.sin_sq_add_cos_sq θ
    linear_combination h + (-(poincareV w 0) * Real.sin F
      + poincareV w 1 * Real.cos F) * this
  have hU : orbitalUnit (poincareF w + θ) = rot θ (orbitalUnit (poincareF w)) := by
    ext i; fin_cases i <;> simp [orbitalUnit, rot, Real.sin_add, Real.cos_add] <;> ring
  have hD : planeDot (rot θ (poincareV w)) (orbitalUnit (poincareF w + θ)) =
      planeDot (poincareV w) (orbitalUnit (poincareF w)) := by
    rw [hU, planeDot_rot]
  have hJ : keplerJac (rot θ (poincareV w)) (poincareF w + θ) =
      keplerJac (poincareV w) (poincareF w) := by
    unfold keplerJac; rw [hD]
  unfold poincare
  simp only [hK, hV, hF, hJ, hU, planeDot_rot, hL]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [quarterTurn, rot] <;> ring

/-- (S3) for one planet: `(-λ, ξ, Λ, -η) ↦ (σq, -σp)`. -/
theorem poincare_reflect {m κ : ℝ} {w : Phase 2} (hw : w ∈ poincareDom) :
    poincare m κ (![-w.1 0, w.1 1], ![w.2 0, -w.2 1]) =
      (sigmaRefl (poincare m κ w).1, -sigmaRefl (poincare m κ w).2) := by
  have hlen := (poincare_facts hw).2.2.2.2.2.1
  have hΓ : poincareGamma ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareGamma w := by
    rw [gamma_mk]; simp [poincareGamma]
  have hK : poincareK ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      poincareK w := by
    simp only [poincareK, hΓ]; simp
  have hV : poincareV ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      sigmaRefl (poincareV w) := by
    simp only [poincareV, hΓ, sigmaRefl]; ext i; fin_cases i <;> simp
  have hlen' : planeLength (sigmaRefl (poincareV w)) < 1 := by
    have : planeLength (sigmaRefl (poincareV w)) = planeLength (poincareV w) := by
      unfold planeLength; congr 1; simp [planeSq_two, sigmaRefl]
    rwa [this]
  have hF : poincareF ((![-w.1 0, w.1 1] : Fin 2 → ℝ), (![w.2 0, -w.2 1] : Fin 2 → ℝ)) =
      -poincareF w := by
    unfold poincareF
    rw [hV]
    simp only [Matrix.cons_val_zero]
    refine keplerLong_unique hlen' ?_
    have h := keplerPhi_keplerLong hlen (w.1 0)
    simp only [keplerPhi] at h ⊢
    simp only [sigmaRefl, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_neg, Real.cos_neg]
    linarith
  have hU : orbitalUnit (-poincareF w) = sigmaRefl (orbitalUnit (poincareF w)) := by
    ext i; fin_cases i <;> simp [orbitalUnit, sigmaRefl]
  have hD : planeDot (sigmaRefl (poincareV w)) (orbitalUnit (-poincareF w)) =
      planeDot (poincareV w) (orbitalUnit (poincareF w)) := by
    rw [hU]; simp [planeDot_two, sigmaRefl]
  have hJ : keplerJac (sigmaRefl (poincareV w)) (-poincareF w) =
      keplerJac (poincareV w) (poincareF w) := by
    unfold keplerJac; rw [hD]
  unfold poincare
  simp only [hK, hV, hF, hJ, hU, planeDot_sigma, Matrix.cons_val_zero]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [quarterTurn, sigmaRefl] <;> ring

end PlanarSymmetries

end KAM.Planetary

end
