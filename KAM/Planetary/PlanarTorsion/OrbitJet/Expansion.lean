/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.OrbitJet.Algebra

/-!
# Planar quartic torsion: the line expansion of the unit-axis orbit

Along a line `v = t w` the unit-axis orbit `p11c_orbit lam (t • w)` is a degree-four jet in `t`
(`orbit_line_isJet`): the Kepler fixed point `y = i (F - λ)` of `y = t (A e^y - B e^{-y}) / 2`
(`isJet_of_fixedPoint`) and the real expansions of `√(1 - x)` and `1 / (1 + √(1 - x))` feed the
jet algebra of `OrbitJet/Jet`, whose assembled coefficients are those of `p11c_orbitJet`
(`OrbitJet/Algebra`).
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Real
open scoped ContDiff

namespace KAM.Planetary.OrbitJet

open KAM KAM.Kepler Jet5

/-! ### Real expansions -/

private theorem sqrt_one_sub_approx {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |√(1 - x) - (1 - x / 2 - x ^ 2 / 8)| ≤ x ^ 3 := by
  set k := √(1 - x) with hk
  set kt := 1 - x / 2 - x ^ 2 / 8 with hkt
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hkt1 : 1 / 2 ≤ kt := by nlinarith
  have hprod : (k - kt) * (k + kt) = -(x ^ 3 / 8 + x ^ 4 / 64) := by
    have : (k - kt) * (k + kt) = k ^ 2 - kt ^ 2 := by ring
    rw [this, hk2, hkt]; ring
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hx4 : x ^ 4 ≤ x ^ 3 / 2 := by nlinarith [mul_nonneg h0 hx3]
  have hx4' : 0 ≤ x ^ 4 := by positivity
  rw [abs_le]
  constructor
  · by_contra h
    have h := not_le.1 h
    have h2 : (k - kt) * (k + kt) ≤ (k - kt) * (1 / 2) :=
      mul_le_mul_of_nonpos_left (by linarith) (by nlinarith)
    nlinarith
  · by_contra h
    have h := not_le.1 h
    nlinarith [mul_pos (show 0 < k - kt by nlinarith) (show 0 < k + kt by linarith)]

private theorem inv_one_add_sqrt_approx {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |1 / (1 + √(1 - x)) - (1 / 2 + x / 8 + x ^ 2 / 16)| ≤ 2 * x ^ 3 := by
  have hk := sqrt_one_sub_approx h0 h1
  set k := √(1 - x) with hkdef
  set kt := 1 - x / 2 - x ^ 2 / 8 with hkt
  set Wt := 1 / 2 + x / 8 + x ^ 2 / 16 with hWt
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hx4 : x ^ 4 ≤ x ^ 3 / 2 := by nlinarith [mul_nonneg h0 hx3]
  have hW : 1 / (1 + k) * (1 + k) = 1 := by field_simp
  set W := 1 / (1 + k) with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hW1 : W ≤ 1 := by
    rw [hWdef, div_le_one (by linarith)]; linarith
  have hWt1 : Wt ≤ 1 := by nlinarith
  have hWt0 : 0 ≤ Wt := by nlinarith
  have e1 : W - Wt = W * ((3 * x ^ 3 / 64 + x ^ 4 / 128) - Wt * (k - kt)) := by
    have : W - Wt - W * ((3 * x ^ 3 / 64 + x ^ 4 / 128) - Wt * (k - kt)) =
        Wt * (W * (1 + k) - 1) := by
      rw [hWt, hkt]; ring
    rw [hW] at this
    linarith
  rw [e1, abs_mul, abs_of_nonneg hW0]
  have h2 : |(3 * x ^ 3 / 64 + x ^ 4 / 128) - Wt * (k - kt)| ≤ 2 * x ^ 3 := by
    have h3 : |Wt * (k - kt)| ≤ x ^ 3 := by
      rw [abs_mul, abs_of_nonneg hWt0]
      calc Wt * |k - kt| ≤ 1 * x ^ 3 := mul_le_mul hWt1 hk (abs_nonneg _) zero_le_one
        _ = x ^ 3 := one_mul _
    have h4 : 0 ≤ 3 * x ^ 3 / 64 + x ^ 4 / 128 := by positivity
    calc _ ≤ |3 * x ^ 3 / 64 + x ^ 4 / 128| + |Wt * (k - kt)| := abs_sub _ _
      _ ≤ x ^ 3 + x ^ 3 := by rw [abs_of_nonneg h4]; nlinarith
      _ = 2 * x ^ 3 := by ring
  calc W * _ ≤ 1 * (2 * x ^ 3) := mul_le_mul hW1 h2 (abs_nonneg _) zero_le_one
    _ = 2 * x ^ 3 := one_mul _

/-! ### The jets of the radial factors -/

private theorem planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeSq_smul' (t : ℝ) (w : Fin 2 → ℝ) : planeSq (t • w) = t ^ 2 * planeSq w := by
  simp only [planeSq_two, Pi.smul_apply, smul_eq_mul]; ring

/-- Eventually `t² c ≤ 1 / 2`. -/
private theorem eventually_sq_le (c : ℝ) : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * c ≤ 1 / 2 := by
  have hc : Continuous fun t : ℝ => t ^ 2 * c := by fun_prop
  have := hc.tendsto 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
  filter_upwards [Metric.tendsto_nhds.1 this (1 / 2) (by norm_num)] with t ht
  have := (le_abs_self _).trans ht.le
  simpa [Real.dist_eq] using this

private theorem eventually_abs_le_one : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
  exact (by simpa using ht : |t| < 1).le

/-- `t⁶ c³ ≤ c³ |t|⁵` for `|t| ≤ 1`. -/
private theorem pow_six_le {t c : ℝ} (hc : 0 ≤ c) (ht : |t| ≤ 1) :
    (t ^ 2 * c) ^ 3 ≤ c ^ 3 * |t| ^ 5 := by
  have h1 : (t ^ 2 * c) ^ 3 = c ^ 3 * |t| ^ 6 := by
    rw [mul_pow, ← sq_abs t]; ring
  rw [h1]
  have : |t| ^ 6 ≤ |t| ^ 5 := pow_le_pow_of_le_one (abs_nonneg t) ht (by norm_num)
  have hc3 : 0 ≤ c ^ 3 := by positivity
  nlinarith

theorem isJet_sqrt (c : ℝ) (hc : 0 ≤ c) :
    IsJet (fun t : ℝ => ((√(1 - t ^ 2 * c) : ℝ) : ℂ)) (kJet (c : ℂ)) := by
  refine IsBigO.of_bound (c ^ 3) ?_
  filter_upwards [eventually_sq_le c, eventually_abs_le_one] with t ht ht1
  have h0 : 0 ≤ t ^ 2 * c := by positivity
  have h := sqrt_one_sub_approx h0 ht
  have e : ((√(1 - t ^ 2 * c) : ℝ) : ℂ) - (kJet (c : ℂ)).ev t =
      (((√(1 - t ^ 2 * c) - (1 - t ^ 2 * c / 2 - (t ^ 2 * c) ^ 2 / 8)) : ℝ) : ℂ) := by
    simp only [Jet5.ev, kJet]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h5 := pow_six_le (t := t) hc ht1
  have : ‖t ^ 5‖ = |t| ^ 5 := by simp
  rw [this]
  linarith

theorem isJet_inv_sqrt (c : ℝ) (hc : 0 ≤ c) :
    IsJet (fun t : ℝ => ((1 / (1 + √(1 - t ^ 2 * c)) : ℝ) : ℂ)) (wJet (c : ℂ)) := by
  refine IsBigO.of_bound (2 * c ^ 3) ?_
  filter_upwards [eventually_sq_le c, eventually_abs_le_one] with t ht ht1
  have h0 : 0 ≤ t ^ 2 * c := by positivity
  have h := inv_one_add_sqrt_approx h0 ht
  have e : ((1 / (1 + √(1 - t ^ 2 * c)) : ℝ) : ℂ) - (wJet (c : ℂ)).ev t =
      (((1 / (1 + √(1 - t ^ 2 * c)) -
        (1 / 2 + t ^ 2 * c / 8 + (t ^ 2 * c) ^ 2 / 16)) : ℝ) : ℂ) := by
    simp only [Jet5.ev, wJet]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h5 := pow_six_le (t := t) hc ht1
  have : ‖t ^ 5‖ = |t| ^ 5 := by simp
  rw [this]
  linarith

end KAM.Planetary.OrbitJet

end
