/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Defs
public import KAM.Planetary.SecularForm.Quartic.PairSymmetry

/-!
# Secular form: the square-root chart `u ↦ v` and its exact inverse

Blueprint P, Part 8, `stepP:p8:q4-a`: the chart `v = (1 - |u|²/(4Λ))^{1/2} u/√Λ` of the Poincaré
variables equals `poincareV`; its inverse `u = √Λ v / ((1 + √(1 - |v|²))/2)^{1/2}` is explicit,
continuous and `O(2)`-equivariant.  Also: scaling of the quartic monomials and the elementary fact
that `a + b s² + c s⁴ = O(s⁵)` forces `c = 0`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

private theorem qca_planeSq_eq (x : Fin 2 → ℝ) : planeSq x = x 0 ^ 2 + x 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem qca_planeDot_eq (x y : Fin 2 → ℝ) : planeDot x y = x 0 * y 0 + x 1 * y 1 := by
  simp [planeDot, Fin.sum_univ_two]

/-- The square-root chart of the Poincaré variables. -/
def sqrtChart (L : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (√(1 - planeSq x / (4 * L)) / √L) • x

/-- The exact inverse of `sqrtChart`. -/
def sqrtChartInv (L : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (√L / √((1 + √(1 - planeSq x)) / 2)) • x

theorem planeSq_smul_vec (c : ℝ) (x : Fin 2 → ℝ) : planeSq (c • x) = c ^ 2 * planeSq x := by
  simp only [qca_planeSq_eq, Pi.smul_apply, smul_eq_mul]; ring

theorem planeDot_smul_vec (c e : ℝ) (x y : Fin 2 → ℝ) :
    planeDot (c • x) (e • y) = c * e * planeDot x y := by
  simp only [qca_planeDot_eq, Pi.smul_apply, smul_eq_mul]; ring

theorem quarticMonomials_smul_vec (c : ℝ) (x y : Fin 2 → ℝ) (k : Fin 6) :
    quarticMonomials (c • x) (c • y) k = c ^ 4 * quarticMonomials x y k := by
  fin_cases k <;>
    simp [quarticMonomials, planeSq_smul_vec, planeDot_smul_vec] <;> ring

theorem poincareV_pair (L : ℝ) (hL : 0 < L) (x : Fin 2 → ℝ) :
    poincareV (![0, x 0], ![L, x 1]) = sqrtChart L x := by
  have e : (1 - poincareGamma (![0, x 0], ![L, x 1]) / (2 * L)) / L =
      (1 - planeSq x / (4 * L)) / L := by
    simp only [poincareGamma, qca_planeSq_eq, Matrix.cons_val_one, Matrix.cons_val_zero]
    congr 2
    field_simp
    ring
  have e2 : (![x 0, x 1] : Fin 2 → ℝ) = x := by ext k; fin_cases k <;> rfl
  simp only [poincareV, Matrix.cons_val_one, Matrix.cons_val_zero, sqrtChart]
  rw [e, Real.sqrt_div' _ hL.le, e2]

theorem continuous_planeSq_vec : Continuous fun x : Fin 2 → ℝ => planeSq x := by
  unfold planeSq; fun_prop

theorem continuous_sqrtChart (L : ℝ) : Continuous (sqrtChart L) := by
  unfold sqrtChart
  have := continuous_planeSq_vec
  fun_prop

theorem sqrtChart_zero (L : ℝ) : sqrtChart L 0 = 0 := smul_zero _

theorem continuous_sqrtChartInv (L : ℝ) : Continuous (sqrtChartInv L) := by
  unfold sqrtChartInv
  have h1 := continuous_planeSq_vec
  have h2 : Continuous fun x : Fin 2 → ℝ => √((1 + √(1 - planeSq x)) / 2) := by fun_prop
  refine Continuous.smul (Continuous.div (by fun_prop) h2 fun x => ?_) continuous_id
  have : 0 < (1 + √(1 - planeSq x)) / 2 := by positivity
  exact (Real.sqrt_pos.2 this).ne'

theorem sqrtChartInv_zero (L : ℝ) : sqrtChartInv L 0 = 0 := smul_zero _

theorem planeSq_mulVec {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.transpose * R = 1)
    (x : Fin 2 → ℝ) : planeSq (R.mulVec x) = planeSq x := by
  have h00 := congrFun (congrFun hR 0) 0
  have h11 := congrFun (congrFun hR 1) 1
  have h01 := congrFun (congrFun hR 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11 h01
  simp only [qca_planeSq_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (x 0) ^ 2 * h00 + (x 1) ^ 2 * h11 + 2 * x 0 * x 1 * h01

theorem sqrtChartInv_mulVec {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.transpose * R = 1) (L : ℝ)
    (x : Fin 2 → ℝ) : sqrtChartInv L (R.mulVec x) = R.mulVec (sqrtChartInv L x) := by
  simp only [sqrtChartInv, planeSq_mulVec hR, Matrix.mulVec_smul]

theorem sqrtChart_sqrtChartInv {L : ℝ} (hL : 0 < L) {x : Fin 2 → ℝ} (hx : planeSq x < 1) :
    sqrtChart L (sqrtChartInv L x) = x := by
  set q := planeSq x with hq
  have hq0 : 0 ≤ q := by rw [hq, qca_planeSq_eq]; positivity
  set k := √(1 - q) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hs0 : 0 < (1 + k) / 2 := by positivity
  set s := √((1 + k) / 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hs0
  have hs2 : s ^ 2 = (1 + k) / 2 := Real.sq_sqrt hs0.le
  have hLs : 0 < √L := Real.sqrt_pos.2 hL
  have e : 1 - planeSq ((√L / s) • x) / (4 * L) = s ^ 2 := by
    rw [planeSq_smul_vec, ← hq, div_pow, Real.sq_sqrt hL.le, hs2]
    have : q = 1 - k ^ 2 := by linarith
    rw [this]
    field_simp
    ring
  unfold sqrtChart sqrtChartInv
  rw [← hk, ← hs, e, Real.sqrt_sq hspos.le, smul_smul]
  have : s / √L * (√L / s) = 1 := by field_simp
  rw [this, one_smul]

/-- A trinomial `a + b s² + c s⁴` that is `O(s⁵)` at `0` has vanishing quartic coefficient. -/
theorem quartic_coeff_eq_zero_of_isBigO {a b c : ℝ}
    (h : (fun s : ℝ => a + b * s ^ 2 + c * s ^ 4) =O[𝓝 0] fun s => ‖s‖ ^ 5) : c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  rw [Metric.eventually_nhds_iff] at hC
  obtain ⟨ε, hε, hball⟩ := hC
  have hb : ∀ s : ℝ, |s| < ε → |a + b * s ^ 2 + c * s ^ 4| ≤ C * |s| ^ 5 := fun s hs => by
    have := hball (y := s) (by simpa [Real.dist_eq] using hs)
    simpa [Real.norm_eq_abs, abs_pow] using this
  have ha : a = 0 := by
    have := hb 0 (by simpa using hε)
    simp at this
    exact this
  subst ha
  by_contra hc0
  have hcpos : 0 < |c| := abs_pos.2 hc0
  have hC1 : 0 < |C| + 1 := by positivity
  set t : ℝ := min (ε / 4) (|c| / (6 * (|C| + 1))) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ ε / 4 := min_le_left _ _
  have ht2 : t ≤ |c| / (6 * (|C| + 1)) := min_le_right _ _
  have h1 := hb t (by rw [abs_of_pos htpos]; linarith)
  have h2 := hb (2 * t) (by rw [abs_of_pos (by positivity)]; linarith)
  have e : (0 + b * (2 * t) ^ 2 + c * (2 * t) ^ 4) - 4 * (0 + b * t ^ 2 + c * t ^ 4) =
      12 * c * t ^ 4 := by ring
  have h3 : |12 * c * t ^ 4| ≤ C * (2 * t) ^ 5 + 4 * (C * t ^ 5) := by
    rw [← e]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos htpos] at h1
    rw [abs_of_pos (by positivity : (0:ℝ) < 2 * t)] at h2
    rw [abs_mul, abs_of_pos (show (0:ℝ) < 4 by norm_num)]
    linarith
  have h3' : 12 * |c| * t ^ 4 ≤ C * (2 * t) ^ 5 + 4 * (C * t ^ 5) := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 12),
      abs_of_pos (by positivity : 0 < t ^ 4)] at h3
    exact h3
  have h4 : 12 * |c| * t ^ 4 ≤ 36 * |C| * t * t ^ 4 := by
    have : C * (2 * t) ^ 5 + 4 * (C * t ^ 5) = 36 * C * t * t ^ 4 := by ring
    have h5 : 36 * C * t * t ^ 4 ≤ 36 * |C| * t * t ^ 4 := by
      have := le_abs_self C
      have : 0 ≤ t * t ^ 4 := by positivity
      nlinarith
    linarith
  have h6 : 12 * |c| ≤ 36 * |C| * t := by
    have : 0 < t ^ 4 := by positivity
    nlinarith
  have h7 : t * (6 * (|C| + 1)) ≤ |c| := by
    rwa [le_div_iff₀ (by positivity)] at ht2
  nlinarith [abs_nonneg C]

end SecularForm
end KAM.Planetary
end
