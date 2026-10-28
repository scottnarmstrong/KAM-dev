/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.TwoPlanets

/-!
# Good axes: two planets

Blueprint P, Part 10 (`bpP:p10:n2`, `stepP:p10:n2-r`, `stepP:p10:n2-t`, `stepP:p10:n2-nr`): for two
planets the ratio `tr² / det` of the secular matrix is explicit, bounded below by `Λ₂/Λ₁ + 2`, controls
the eigenvalue ratio, and forces non-resonance in the hierarchical regime.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

section N2Aux
variable (D : Data 2) {a : Vec 2}

/-- `stepP:p10:n2-r`: the exact trace-determinant ratio. -/
lemma ratio_formula (ha : a ∈ axes 2) :
    (coeffs D a).trace^2/(coeffs D a).det =
      (action D a 0+action D a 1)^2/(action D a 0*action D a 1) /
        (1-(pairB D a 0 1/pairA D a 0 1)^2) := by
  have h0 := SecularSpectrum.action_pos D ha 0
  have h1 := SecularSpectrum.action_pos D ha 1
  have hA := pairA_pos D ha (j := 0) (k := 1) (by decide)
  have hd := pairA_sub_pairB_pos D ha (j := 0) (k := 1) (by decide)
  have hB := pairB_pos D ha (j := 0) (k := 1) (by decide)
  have hAB : pairA D a 0 1 ^ 2 - pairB D a 0 1 ^ 2 ≠ 0 := by nlinarith
  rw [trace_two, det_two D ha]
  generalize pairA D a 0 1 = A at *
  generalize pairB D a 0 1 = B at *
  generalize action D a 0 = x at *
  generalize action D a 1 = y at *
  have hA' : 1 - (B / A) ^ 2 = (A ^ 2 - B ^ 2) / A ^ 2 := by field_simp
  rw [hA']
  field_simp
  ring

lemma ratio_gt (ha : a ∈ axes 2) :
    (coeffs D a).trace^2/(coeffs D a).det > action D a 1/action D a 0+2 := by
  have h0 := SecularSpectrum.action_pos D ha 0
  have h1 := SecularSpectrum.action_pos D ha 1
  have hA := pairA_pos D ha (j := 0) (k := 1) (by decide)
  have hd := pairA_sub_pairB_pos D ha (j := 0) (k := 1) (by decide)
  have hB := pairB_pos D ha (j := 0) (k := 1) (by decide)
  rw [ratio_formula D ha]
  have hq : 0 < pairB D a 0 1 / pairA D a 0 1 := div_pos hB hA
  have hq1 : pairB D a 0 1 / pairA D a 0 1 < 1 := (div_lt_one hA).2 (by linarith)
  have hf : 0 < 1 - (pairB D a 0 1 / pairA D a 0 1) ^ 2 := by nlinarith
  have hf1 : 1 - (pairB D a 0 1 / pairA D a 0 1) ^ 2 < 1 := by nlinarith
  have hX : action D a 1 / action D a 0 + 2 <
      (action D a 0 + action D a 1) ^ 2 / (action D a 0 * action D a 1) := by
    have : (action D a 0 + action D a 1) ^ 2 / (action D a 0 * action D a 1) =
        action D a 1 / action D a 0 + 2 + action D a 0 / action D a 1 := by
      field_simp; ring
    rw [this]
    have := div_pos h0 h1
    linarith
  have hXp : 0 < (action D a 0 + action D a 1) ^ 2 / (action D a 0 * action D a 1) := by
    positivity
  rw [gt_iff_lt, lt_div_iff₀ hf]
  nlinarith

/-- `stepP:p10:n2-t`. -/
lemma sigma_ratio_ge (ha : a ∈ axes 2) :
    sigma D a 0/sigma D a 1 ≥ (coeffs D a).trace^2/(coeffs D a).det-3 := by
  have hlt := sigma_two_lt D ha
  have n1 := sigma_two_neg D ha 1
  have n0 := sigma_two_neg D ha 0
  have h1 := sorted_two_sum (coeffs D a) (coeffs_hermitian D a)
  have h2 := sorted_two_prod (coeffs D a) (coeffs_hermitian D a)
  change sigma D a 0 + sigma D a 1 = _ at h1
  change sigma D a 0 * sigma D a 1 = _ at h2
  rw [← h1, ← h2]
  generalize sigma D a 0 = s at *
  generalize sigma D a 1 = t at *
  have hst : 0 < s * t := mul_pos_of_neg_of_neg n0 n1
  have e : (s + t) ^ 2 / (s * t) = s / t + t / s + 2 := by
    have := n0.ne; have := n1.ne
    field_simp; ring
  rw [e, ge_iff_le]
  have : t / s < 1 := by
    rw [div_lt_one_of_neg n0]; exact hlt
  linarith

lemma action_ratio_ge (ha : a ∈ axes 2) (h : 16 * D.m 0 ^ 2 / D.m 1 ^ 2 ≤ a 1 / a 0) :
    4 ≤ action D a 1 / action D a 0 := by
  have a0 := ha.1 0
  have a1 := ha.1 1
  have m0 := D.hm 0
  have m1 := D.hm 1
  have hG := D.hG
  have hm0 := D.hm0
  have hk : 0 < D.G * D.m0 := mul_pos hG hm0
  have h' : 16 * D.m 0 ^ 2 / D.m 1 ^ 2 * a 0 ≤ a 1 := by
    rwa [le_div_iff₀ a0] at h
  have hsq : (4 * D.m 0 / D.m 1) ^ 2 = 16 * D.m 0 ^ 2 / D.m 1 ^ 2 := by field_simp; ring
  have hs0 : 0 < √(D.G * D.m0 * a 0) := Real.sqrt_pos.2 (mul_pos hk a0)
  have hroot : 4 * D.m 0 / D.m 1 * √(D.G * D.m0 * a 0) ≤ √(D.G * D.m0 * a 1) := by
    have hle : (4 * D.m 0 / D.m 1) ^ 2 * (D.G * D.m0 * a 0) ≤ D.G * D.m0 * a 1 := by
      rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_left h' hk.le]
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at this
  have hA0 : 0 < action D a 0 := SecularSpectrum.action_pos D ha 0
  rw [le_div_iff₀ hA0]
  simp only [action]
  have := mul_le_mul_of_nonneg_left hroot m1.le
  calc 4 * (D.m 0 * √(D.G * D.m0 * a 0))
      = D.m 1 * (4 * D.m 0 / D.m 1 * √(D.G * D.m0 * a 0)) := by field_simp
    _ ≤ _ := this

/-- `stepP:p10:n2-nr`. -/
lemma nr4_of_hier (ha : a ∈ axes 2) (h : 16 * D.m 0 ^ 2 / D.m 1 ^ 2 ≤ a 1 / a 0) :
    nr4 (sigma D a) := by
  have hlt := sigma_two_lt D ha
  have n1 := sigma_two_neg D ha 1
  have n0 := sigma_two_neg D ha 0
  have h4 := action_ratio_ge D ha h
  have hr := ratio_gt D ha
  have hge := sigma_ratio_ge D ha
  have h1 := sorted_two_sum (coeffs D a) (coeffs_hermitian D a)
  have h2 := sorted_two_prod (coeffs D a) (coeffs_hermitian D a)
  change sigma D a 0 + sigma D a 1 = _ at h1
  change sigma D a 0 * sigma D a 1 = _ at h2
  rw [nr4_two_iff D ha]
  have he : (coeffs D a).trace^2/(coeffs D a).det =
      sigma D a 0 / sigma D a 1 + sigma D a 1 / sigma D a 0 + 2 := by
    rw [← h1, ← h2]
    generalize sigma D a 0 = s at *
    generalize sigma D a 1 = t at *
    have := n0.ne; have := n1.ne
    field_simp
    ring
  have hinv : sigma D a 1 / sigma D a 0 = (sigma D a 0 / sigma D a 1)⁻¹ := (inv_div _ _).symm
  rw [hinv] at he
  have hsum : 4 < sigma D a 0 / sigma D a 1 + (sigma D a 0 / sigma D a 1)⁻¹ := by linarith
  generalize sigma D a 0 / sigma D a 1 = t at *
  constructor
  · rintro rfl
    norm_num at hsum
  · rintro rfl
    norm_num at hsum

end N2Aux

theorem n2 (D : Data 2) {a : Vec 2} (ha : a ∈ axes 2) :
    (coeffs D a).trace^2/(coeffs D a).det =
      (action D a 0+action D a 1)^2/(action D a 0*action D a 1) /
        (1-(pairB D a 0 1/pairA D a 0 1)^2) ∧
    (coeffs D a).trace^2/(coeffs D a).det > action D a 1/action D a 0+2 ∧
    sigma D a 0/sigma D a 1 ≥ (coeffs D a).trace^2/(coeffs D a).det-3 ∧
    (16*D.m 0^2/D.m 1^2 ≤ a 1/a 0 → nr4 (sigma D a)) :=
  ⟨ratio_formula D ha, ratio_gt D ha, sigma_ratio_ge D ha, nr4_of_hier D ha⟩

end Nondegeneracy
end KAM.Planetary
end
