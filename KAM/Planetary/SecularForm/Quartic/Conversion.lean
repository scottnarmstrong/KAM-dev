/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Defs

/-!
# Secular form: the square-root conversion between eccentricity vectors and canonical coordinates

Blueprint P, Part 8, `stepP:p8:q4-a`: the passage `v = (1 - |u|²/(4Λ))^{1/2} u / √Λ` from the
eccentricity vectors `v` to the canonical coordinates `u` is exact; the quartic part in `u` of a
function with quadratic part `A|v₁|² + A'|v₂|² + B v₁·v₂` and quartic part `W₄` in `v` is `W₄(u/√Λ)`
minus the correction `A/4 |u₁|⁴/Λ₁² + A'/4 |u₂|⁴/Λ₂² + B/8 (u₁·u₂)/√(Λ₁Λ₂) (|u₁|²/Λ₁ + |u₂|²/Λ₂)`
(the expansion of `(1 - t)^{1/2}` with `t = |u|²/(4Λ)`).
-/

@[expose] public noncomputable section
open Set Filter Asymptotics
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

private theorem qcv_planeSq_eq (x : Fin 2 → ℝ) : planeSq x = x 0 ^ 2 + x 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem qcv_planeDot_eq (x y : Fin 2 → ℝ) : planeDot x y = x 0 * y 0 + x 1 * y 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem qcv_planeSq_smul (c : ℝ) (x : Fin 2 → ℝ) :
    planeSq (c • x) = c ^ 2 * planeSq x := by
  simp only [qcv_planeSq_eq, Pi.smul_apply, smul_eq_mul]; ring

private theorem qcv_planeDot_smul (c e : ℝ) (x y : Fin 2 → ℝ) :
    planeDot (c • x) (e • y) = c * e * planeDot x y := by
  simp only [qcv_planeDot_eq, Pi.smul_apply, smul_eq_mul]; ring

private theorem qcv_planeSq_le (x : Fin 2 → ℝ) : planeSq x ≤ 2 * ‖x‖ ^ 2 := by
  have h0 : x 0 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sq_abs (x 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm x 0) 2
  have h1 : x 1 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sq_abs (x 1)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm x 1) 2
  rw [qcv_planeSq_eq]; linarith

private theorem qcv_planeSq_nonneg (x : Fin 2 → ℝ) : 0 ≤ planeSq x := by
  rw [qcv_planeSq_eq]; positivity

private theorem qcv_abs_planeDot_le (x y : Fin 2 → ℝ) : |planeDot x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  have hx : ∀ k, |x k| ≤ ‖x‖ := fun k => by simpa using norm_le_pi_norm x k
  have hy : ∀ k, |y k| ≤ ‖y‖ := fun k => by simpa using norm_le_pi_norm y k
  have h0 : |x 0 * y 0| ≤ ‖x‖ * ‖y‖ := by
    rw [abs_mul]; exact mul_le_mul (hx 0) (hy 0) (abs_nonneg _) (norm_nonneg _)
  have h1 : |x 1 * y 1| ≤ ‖x‖ * ‖y‖ := by
    rw [abs_mul]; exact mul_le_mul (hx 1) (hy 1) (abs_nonneg _) (norm_nonneg _)
  rw [qcv_planeDot_eq]
  calc _ ≤ |x 0 * y 0| + |x 1 * y 1| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Elementary facts on `s = √(1 - t)`: with `δ = 1 - s` one has `t = δ (2 - δ)`. -/
private theorem qcv_sqrt (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 4) :
    √(1 - t) ^ 2 = 1 - t ∧ 0 ≤ √(1 - t) ∧ √(1 - t) ≤ 1 ∧ 1 - √(1 - t) ≤ t ∧
      |√(1 - t) - 1 + t / 2| ≤ t ^ 2 / 2 := by
  have hs2 : √(1 - t) ^ 2 = 1 - t := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ √(1 - t) := Real.sqrt_nonneg _
  have hs1 : √(1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  refine ⟨hs2, hs0, hs1, ?_, ?_⟩
  · nlinarith
  · have hd : √(1 - t) - 1 + t / 2 = -((1 - √(1 - t)) ^ 2 / 2) := by nlinarith
    rw [hd, abs_neg, abs_of_nonneg (by positivity)]
    have : 1 - √(1 - t) ≤ t := by nlinarith
    have h2 : 0 ≤ 1 - √(1 - t) := by linarith
    nlinarith

private theorem qcv_qm (a b : ℝ) (x y : Fin 2 → ℝ) :
    quarticMonomials (a • x) (b • y) = ![(a ^ 2 * planeSq x) ^ 2, (b ^ 2 * planeSq y) ^ 2,
      a ^ 2 * planeSq x * (b ^ 2 * planeSq y), (a * b * planeDot x y) ^ 2,
      a ^ 2 * planeSq x * (a * b * planeDot x y), b ^ 2 * planeSq y * (a * b * planeDot x y)] := by
  simp only [quarticMonomials, qcv_planeSq_smul, qcv_planeDot_smul]

private theorem qcv_tail_eq {Λ₁ Λ₂ ρ₁ ρ₂ p q d X₁ X₂ π A A' B : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hΛ₁ : ρ₁ ^ 2 = Λ₁) (hΛ₂ : ρ₂ ^ 2 = Λ₂)
    (hX₁ : X₁ = (1 - p / (4 * Λ₁)) / Λ₁) (hX₂ : X₂ = (1 - q / (4 * Λ₂)) / Λ₂) :
    (A * (X₁ * p) + A' * (X₂ * q) + B * (π / (ρ₁ * ρ₂) * d)) -
      (A * (p / Λ₁) + A' * (q / Λ₂) + B * (d / (ρ₁ * ρ₂))) +
      (A / 4 * p ^ 2 / Λ₁ ^ 2 + A' / 4 * q ^ 2 / Λ₂ ^ 2 +
        B / 8 * (d / (ρ₁ * ρ₂)) * (p / Λ₁ + q / Λ₂)) = 
      B * d / (ρ₁ * ρ₂) * (π - 1 + (p / (4 * Λ₁) + q / (4 * Λ₂)) / 2) := by
  subst hX₁ hX₂
  rw [← hΛ₁, ← hΛ₂]
  field_simp
  ring

private theorem qcv_quartic_eq (c : Fin 6 → ℝ) {Λ₁ Λ₂ ρ₁ ρ₂ a₁ a₂ π : ℝ} (x y : Fin 2 → ℝ)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hΛ₁ : ρ₁ ^ 2 = Λ₁) (hΛ₂ : ρ₂ ^ 2 = Λ₂)
    (ha₁ : a₁ ^ 2 = (1 - planeSq x / (4 * Λ₁)) / Λ₁)
    (ha₂ : a₂ ^ 2 = (1 - planeSq y / (4 * Λ₂)) / Λ₂) (hπ : a₁ * a₂ = π / (ρ₁ * ρ₂)) :
    ∑ m, c m * quarticMonomials (a₁ • x) (a₂ • y) m -
        ∑ m, c m * quarticMonomials (ρ₁⁻¹ • x) (ρ₂⁻¹ • y) m =
      c 0 * (planeSq x ^ 2 / Λ₁ ^ 2) * ((1 - planeSq x / (4 * Λ₁)) ^ 2 - 1) +
      c 1 * (planeSq y ^ 2 / Λ₂ ^ 2) * ((1 - planeSq y / (4 * Λ₂)) ^ 2 - 1) +
      c 2 * (planeSq x * planeSq y / (Λ₁ * Λ₂)) *
        ((1 - planeSq x / (4 * Λ₁)) * (1 - planeSq y / (4 * Λ₂)) - 1) +
      c 3 * (planeDot x y ^ 2 / (Λ₁ * Λ₂)) * (π ^ 2 - 1) +
      c 4 * (planeSq x * planeDot x y / (Λ₁ * (ρ₁ * ρ₂))) *
        ((1 - planeSq x / (4 * Λ₁)) * π - 1) +
      c 5 * (planeSq y * planeDot x y / (Λ₂ * (ρ₁ * ρ₂))) *
        ((1 - planeSq y / (4 * Λ₂)) * π - 1) := by
  have hw₁ : (ρ₁⁻¹) ^ 2 = 1 / Λ₁ := by rw [inv_pow, hΛ₁, one_div]
  have hw₂ : (ρ₂⁻¹) ^ 2 = 1 / Λ₂ := by rw [inv_pow, hΛ₂, one_div]
  have hw : ρ₁⁻¹ * ρ₂⁻¹ = 1 / (ρ₁ * ρ₂) := by rw [one_div, mul_inv]
  simp only [Fin.sum_univ_six, qcv_qm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
    Matrix.head_cons, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [ha₁, ha₂, hπ, hw₁, hw₂, hw]
  have e1 : Λ₁ = ρ₁ ^ 2 := hΛ₁.symm
  have e2 : Λ₂ = ρ₂ ^ 2 := hΛ₂.symm
  rw [e1, e2]
  field_simp
  ring

private theorem qcv_term {K x y Bx By : ℝ} (hx : |x| ≤ Bx) (hy : |y| ≤ By) :
    |K * x * y| ≤ |K| * Bx * By := by
  rw [abs_mul, abs_mul]
  have := (abs_nonneg x).trans hx
  have := (abs_nonneg y).trans hy
  gcongr

private theorem qcv_brackets {t₁ t₂ s₁ s₂ ε : ℝ} (ht₁0 : 0 ≤ t₁) (ht₂0 : 0 ≤ t₂)
    (ht₁ : t₁ ≤ ε) (ht₂ : t₂ ≤ ε) (hf₁ : t₁ ≤ 1 / 4) (hf₂ : t₂ ≤ 1 / 4)
    (hs₁ : s₁ ^ 2 = 1 - t₁) (hs₂ : s₂ ^ 2 = 1 - t₂)
    (hs₁0 : 0 ≤ s₁) (hs₂0 : 0 ≤ s₂) (hs₁1 : s₁ ≤ 1) (hs₂1 : s₂ ≤ 1)
    (hm₁ : 1 - s₁ ≤ t₁) (hm₂ : 1 - s₂ ≤ t₂)
    (hσ₁ : |s₁ - 1 + t₁ / 2| ≤ t₁ ^ 2 / 2) (hσ₂ : |s₂ - 1 + t₂ / 2| ≤ t₂ ^ 2 / 2) :
    |s₁ * s₂ - 1 + (t₁ + t₂) / 2| ≤ 2 * ε ^ 2 ∧ |(1 - t₁) ^ 2 - 1| ≤ 3 * ε ∧
      |(1 - t₂) ^ 2 - 1| ≤ 3 * ε ∧ |(1 - t₁) * (1 - t₂) - 1| ≤ 2 * ε ∧
      |(s₁ * s₂) ^ 2 - 1| ≤ 2 * ε ∧ |(1 - t₁) * (s₁ * s₂) - 1| ≤ 3 * ε ∧
      |(1 - t₂) * (s₁ * s₂) - 1| ≤ 3 * ε := by
  have hε : 0 ≤ ε := ht₁0.trans ht₁
  have hπ0 : 0 ≤ s₁ * s₂ := mul_nonneg hs₁0 hs₂0
  have hπ1 : s₁ * s₂ ≤ 1 := by nlinarith
  have hπ2 : 1 - s₁ * s₂ ≤ t₁ + t₂ := by nlinarith
  have hπsq : (s₁ * s₂) ^ 2 = (1 - t₁) * (1 - t₂) := by rw [mul_pow, hs₁, hs₂]
  have b3 : |(1 - t₁) * (1 - t₂) - 1| ≤ 2 * ε := by
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨?_, ?_, ?_, b3, by rw [hπsq]; exact b3, ?_, ?_⟩
  · have h : s₁ * s₂ - 1 + (t₁ + t₂) / 2 = (s₁ - 1 + t₁ / 2) * s₂ +
        (1 - t₁ / 2) * (s₂ - 1 + t₂ / 2) + t₁ * t₂ / 4 := by ring
    have e1 : |(s₁ - 1 + t₁ / 2) * s₂| ≤ t₁ ^ 2 / 2 := by
      rw [abs_mul, abs_of_nonneg hs₂0]
      calc _ ≤ t₁ ^ 2 / 2 * 1 := by gcongr
        _ = _ := mul_one _
    have e2 : |(1 - t₁ / 2) * (s₂ - 1 + t₂ / 2)| ≤ t₂ ^ 2 / 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      calc _ ≤ 1 * (t₂ ^ 2 / 2) := by gcongr; linarith
        _ = _ := one_mul _
    have e3 : |t₁ * t₂ / 4| ≤ t₁ * t₂ / 4 := by rw [abs_of_nonneg (by positivity)]
    have h1 : t₁ ^ 2 ≤ ε ^ 2 := by gcongr
    have h2 : t₂ ^ 2 ≤ ε ^ 2 := by gcongr
    have h3 : t₁ * t₂ ≤ ε ^ 2 := by nlinarith
    rw [h]
    calc _ ≤ |(s₁ - 1 + t₁ / 2) * s₂ + (1 - t₁ / 2) * (s₂ - 1 + t₂ / 2)| + |t₁ * t₂ / 4| :=
          abs_add_le _ _
      _ ≤ |(s₁ - 1 + t₁ / 2) * s₂| + |(1 - t₁ / 2) * (s₂ - 1 + t₂ / 2)| + |t₁ * t₂ / 4| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by nlinarith [sq_nonneg ε]
  · have h0 := mul_nonneg ht₁0 (by linarith : 0 ≤ 1 / 4 - t₁)
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg t₁]
  · have h0 := mul_nonneg ht₂0 (by linarith : 0 ≤ 1 / 4 - t₂)
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg t₂]
  · have h1 : t₁ * (s₁ * s₂) ≤ t₁ := mul_le_of_le_one_right ht₁0 hπ1
    have h2 : 0 ≤ t₁ * (s₁ * s₂) := mul_nonneg ht₁0 hπ0
    have h3 : (1 - t₁) * (s₁ * s₂) = s₁ * s₂ - t₁ * (s₁ * s₂) := by ring
    rw [h3, abs_le]; constructor <;> linarith
  · have h1 : t₂ * (s₁ * s₂) ≤ t₂ := mul_le_of_le_one_right ht₂0 hπ1
    have h2 : 0 ≤ t₂ * (s₁ * s₂) := mul_nonneg ht₂0 hπ0
    have h3 : (1 - t₂) * (s₁ * s₂) = s₁ * s₂ - t₂ * (s₁ * s₂) := by ring
    rw [h3, abs_le]; constructor <;> linarith

private theorem qcv_abs7 (a b c d e f g : ℝ) :
    |a + (b + c + d + e + f + g)| ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
  have h1 := abs_add_le a (b + c + d + e + f + g)
  have h2 := abs_add_le (b + c + d + e + f) g
  have h3 := abs_add_le (b + c + d + e) f
  have h4 := abs_add_le (b + c + d) e
  have h5 := abs_add_le (b + c) d
  have h6 := abs_add_le b c
  linarith

private theorem qcv_tail_bound (c : Fin 6 → ℝ) {Λ₁ Λ₂ ρ₁ ρ₂ p q d τ κ B e₀ e₁ e₂ e₃ e₄ e₅ e₆ : ℝ}
    (hΛ₁ : 0 < Λ₁) (hΛ₂ : 0 < Λ₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hκ : 0 < κ) (hτ : 0 ≤ τ)
    (hp0 : 0 ≤ p) (hp : p ≤ 2 * τ) (hq0 : 0 ≤ q) (hq : q ≤ 2 * τ) (hd : |d| ≤ 2 * τ)
    (h₀ : |e₀| ≤ 2 * (κ * τ) ^ 2) (h₁ : |e₁| ≤ 3 * (κ * τ)) (h₂ : |e₂| ≤ 3 * (κ * τ))
    (h₃ : |e₃| ≤ 2 * (κ * τ)) (h₄ : |e₄| ≤ 2 * (κ * τ)) (h₅ : |e₅| ≤ 3 * (κ * τ))
    (h₆ : |e₆| ≤ 3 * (κ * τ)) :
    |B * d / (ρ₁ * ρ₂) * e₀ + (c 0 * (p ^ 2 / Λ₁ ^ 2) * e₁ + c 1 * (q ^ 2 / Λ₂ ^ 2) * e₂ +
      c 2 * (p * q / (Λ₁ * Λ₂)) * e₃ + c 3 * (d ^ 2 / (Λ₁ * Λ₂)) * e₄ +
      c 4 * (p * d / (Λ₁ * (ρ₁ * ρ₂))) * e₅ + c 5 * (q * d / (Λ₂ * (ρ₁ * ρ₂))) * e₆)| ≤
    (4 * κ ^ 2 * |B| / (ρ₁ * ρ₂) + κ * (12 * |c 0| / Λ₁ ^ 2 + 12 * |c 1| / Λ₂ ^ 2 +
      8 * |c 2| / (Λ₁ * Λ₂) + 8 * |c 3| / (Λ₁ * Λ₂) + 12 * |c 4| / (Λ₁ * (ρ₁ * ρ₂)) +
      12 * |c 5| / (Λ₂ * (ρ₁ * ρ₂)))) * τ ^ 3 := by
  have hρ : 0 < ρ₁ * ρ₂ := mul_pos hρ₁ hρ₂
  have hp2 : p ^ 2 ≤ 4 * τ ^ 2 := by nlinarith
  have hq2 : q ^ 2 ≤ 4 * τ ^ 2 := by nlinarith
  have hd2 : d ^ 2 ≤ 4 * τ ^ 2 := by nlinarith [abs_nonneg d, sq_abs d]
  have hpq : p * q ≤ 4 * τ ^ 2 := by nlinarith
  have hpd : |p * d| ≤ 4 * τ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hp0]; nlinarith [abs_nonneg d]
  have hqd : |q * d| ≤ 4 * τ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hq0]; nlinarith [abs_nonneg d]
  have inv1 : |p ^ 2 / Λ₁ ^ 2| ≤ 4 * τ ^ 2 / Λ₁ ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; gcongr
  have inv2 : |q ^ 2 / Λ₂ ^ 2| ≤ 4 * τ ^ 2 / Λ₂ ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; gcongr
  have inv3 : |p * q / (Λ₁ * Λ₂)| ≤ 4 * τ ^ 2 / (Λ₁ * Λ₂) := by
    rw [abs_of_nonneg (by positivity)]; gcongr
  have inv4 : |d ^ 2 / (Λ₁ * Λ₂)| ≤ 4 * τ ^ 2 / (Λ₁ * Λ₂) := by
    rw [abs_of_nonneg (by positivity)]; gcongr
  have inv5 : |p * d / (Λ₁ * (ρ₁ * ρ₂))| ≤ 4 * τ ^ 2 / (Λ₁ * (ρ₁ * ρ₂)) := by
    rw [abs_div, abs_of_pos (show 0 < Λ₁ * (ρ₁ * ρ₂) by positivity)]; gcongr
  have inv6 : |q * d / (Λ₂ * (ρ₁ * ρ₂))| ≤ 4 * τ ^ 2 / (Λ₂ * (ρ₁ * ρ₂)) := by
    rw [abs_div, abs_of_pos (show 0 < Λ₂ * (ρ₁ * ρ₂) by positivity)]; gcongr
  have T0 : |B * d / (ρ₁ * ρ₂) * e₀| ≤ |B| / (ρ₁ * ρ₂) * (2 * τ) * (2 * (κ * τ) ^ 2) := by
    have h := qcv_term (K := B / (ρ₁ * ρ₂)) hd h₀
    rw [abs_div, abs_of_pos hρ, show B / (ρ₁ * ρ₂) * d = B * d / (ρ₁ * ρ₂) by ring] at h
    exact h
  have T1 := qcv_term (K := c 0) inv1 h₁
  have T2 := qcv_term (K := c 1) inv2 h₂
  have T3 := qcv_term (K := c 2) inv3 h₃
  have T4 := qcv_term (K := c 3) inv4 h₄
  have T5 := qcv_term (K := c 4) inv5 h₅
  have T6 := qcv_term (K := c 5) inv6 h₆
  refine (qcv_abs7 _ _ _ _ _ _ _).trans ?_
  have key : |B| / (ρ₁ * ρ₂) * (2 * τ) * (2 * (κ * τ) ^ 2) +
      |c 0| * (4 * τ ^ 2 / Λ₁ ^ 2) * (3 * (κ * τ)) + |c 1| * (4 * τ ^ 2 / Λ₂ ^ 2) * (3 * (κ * τ)) +
      |c 2| * (4 * τ ^ 2 / (Λ₁ * Λ₂)) * (2 * (κ * τ)) +
      |c 3| * (4 * τ ^ 2 / (Λ₁ * Λ₂)) * (2 * (κ * τ)) +
      |c 4| * (4 * τ ^ 2 / (Λ₁ * (ρ₁ * ρ₂))) * (3 * (κ * τ)) +
      |c 5| * (4 * τ ^ 2 / (Λ₂ * (ρ₁ * ρ₂))) * (3 * (κ * τ)) =
    (4 * κ ^ 2 * |B| / (ρ₁ * ρ₂) + κ * (12 * |c 0| / Λ₁ ^ 2 + 12 * |c 1| / Λ₂ ^ 2 +
      8 * |c 2| / (Λ₁ * Λ₂) + 8 * |c 3| / (Λ₁ * Λ₂) + 12 * |c 4| / (Λ₁ * (ρ₁ * ρ₂)) +
      12 * |c 5| / (Λ₂ * (ρ₁ * ρ₂)))) * τ ^ 3 := by
    field_simp
    ring
  rw [← key]
  linarith

private theorem qcv_tail_pt (c : Fin 6 → ℝ) (A A' B : ℝ) {Λ₁ Λ₂ τ κ : ℝ} (x y : Fin 2 → ℝ)
    (hΛ₁ : 0 < Λ₁) (hΛ₂ : 0 < Λ₂) (hτ : 0 ≤ τ) (hκ₁ : 1 / (2 * Λ₁) ≤ κ)
    (hκ₂ : 1 / (2 * Λ₂) ≤ κ) (hx : planeSq x ≤ 2 * τ) (hy : planeSq y ≤ 2 * τ)
    (hxΛ : 2 * τ ≤ Λ₁) (hyΛ : 2 * τ ≤ Λ₂) (hd : |planeDot x y| ≤ 2 * τ) :
    |(A * planeSq ((√(1 - planeSq x / (4 * Λ₁)) / √Λ₁) • x) +
        A' * planeSq ((√(1 - planeSq y / (4 * Λ₂)) / √Λ₂) • y) +
        B * planeDot ((√(1 - planeSq x / (4 * Λ₁)) / √Λ₁) • x)
          ((√(1 - planeSq y / (4 * Λ₂)) / √Λ₂) • y)) -
      (A * (planeSq x / Λ₁) + A' * (planeSq y / Λ₂) + B * (planeDot x y / (√Λ₁ * √Λ₂))) +
      (A / 4 * planeSq x ^ 2 / Λ₁ ^ 2 + A' / 4 * planeSq y ^ 2 / Λ₂ ^ 2 +
        B / 8 * (planeDot x y / (√Λ₁ * √Λ₂)) * (planeSq x / Λ₁ + planeSq y / Λ₂)) +
      (∑ m, c m * quarticMonomials ((√(1 - planeSq x / (4 * Λ₁)) / √Λ₁) • x)
          ((√(1 - planeSq y / (4 * Λ₂)) / √Λ₂) • y) m -
        ∑ m, c m * quarticMonomials ((√Λ₁)⁻¹ • x) ((√Λ₂)⁻¹ • y) m)| ≤
    (4 * κ ^ 2 * |B| / (√Λ₁ * √Λ₂) + κ * (12 * |c 0| / Λ₁ ^ 2 + 12 * |c 1| / Λ₂ ^ 2 +
      8 * |c 2| / (Λ₁ * Λ₂) + 8 * |c 3| / (Λ₁ * Λ₂) + 12 * |c 4| / (Λ₁ * (√Λ₁ * √Λ₂)) +
      12 * |c 5| / (Λ₂ * (√Λ₁ * √Λ₂)))) * τ ^ 3 := by
  have hρ₁ : 0 < √Λ₁ := Real.sqrt_pos.2 hΛ₁
  have hρ₂ : 0 < √Λ₂ := Real.sqrt_pos.2 hΛ₂
  have hΛ₁' : √Λ₁ ^ 2 = Λ₁ := Real.sq_sqrt hΛ₁.le
  have hΛ₂' : √Λ₂ ^ 2 = Λ₂ := Real.sq_sqrt hΛ₂.le
  have hp0 := qcv_planeSq_nonneg x
  have hq0 := qcv_planeSq_nonneg y
  have hκ : 0 < κ := lt_of_lt_of_le (by positivity) hκ₁
  have ht₁0 : 0 ≤ planeSq x / (4 * Λ₁) := by positivity
  have ht₂0 : 0 ≤ planeSq y / (4 * Λ₂) := by positivity
  have hp1 : planeSq x ≤ Λ₁ := hx.trans hxΛ
  have hq1 : planeSq y ≤ Λ₂ := hy.trans hyΛ
  have hf₁ : planeSq x / (4 * Λ₁) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hf₂ : planeSq y / (4 * Λ₂) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hκt₁ : planeSq x / (4 * Λ₁) ≤ κ * τ := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 * Λ₁) * τ * (4 * Λ₁) = 2 * τ := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_right hκ₁ hτ, mul_pos hκ hΛ₁]
  have hκt₂ : planeSq y / (4 * Λ₂) ≤ κ * τ := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 * Λ₂) * τ * (4 * Λ₂) = 2 * τ := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_right hκ₂ hτ, mul_pos hκ hΛ₂]
  obtain ⟨hs₁, hs₁0, hs₁1, hm₁, hσ₁⟩ := qcv_sqrt _ ht₁0 hf₁
  obtain ⟨hs₂, hs₂0, hs₂1, hm₂, hσ₂⟩ := qcv_sqrt _ ht₂0 hf₂
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := qcv_brackets ht₁0 ht₂0 hκt₁ hκt₂ hf₁ hf₂ hs₁ hs₂
    hs₁0 hs₂0 hs₁1 hs₂1 hm₁ hm₂ hσ₁ hσ₂
  have ha₁ : (√(1 - planeSq x / (4 * Λ₁)) / √Λ₁) ^ 2 = (1 - planeSq x / (4 * Λ₁)) / Λ₁ := by
    rw [div_pow, hs₁, hΛ₁']
  have ha₂ : (√(1 - planeSq y / (4 * Λ₂)) / √Λ₂) ^ 2 = (1 - planeSq y / (4 * Λ₂)) / Λ₂ := by
    rw [div_pow, hs₂, hΛ₂']
  have hπ : (√(1 - planeSq x / (4 * Λ₁)) / √Λ₁) * (√(1 - planeSq y / (4 * Λ₂)) / √Λ₂) =
      (√(1 - planeSq x / (4 * Λ₁)) * √(1 - planeSq y / (4 * Λ₂))) / (√Λ₁ * √Λ₂) :=
    div_mul_div_comm _ _ _ _
  have hA := qcv_tail_eq (A := A) (A' := A') (B := B) (p := planeSq x) (q := planeSq y)
    (d := planeDot x y) (π := √(1 - planeSq x / (4 * Λ₁)) * √(1 - planeSq y / (4 * Λ₂)))
    hρ₁ hρ₂ hΛ₁' hΛ₂' (X₁ := (√(1 - planeSq x / (4 * Λ₁)) / √Λ₁) ^ 2)
    (X₂ := (√(1 - planeSq y / (4 * Λ₂)) / √Λ₂) ^ 2) ha₁ ha₂
  have hQ := qcv_quartic_eq c x y hρ₁ hρ₂ hΛ₁' hΛ₂' ha₁ ha₂ hπ
  rw [qcv_planeSq_smul, qcv_planeSq_smul, qcv_planeDot_smul, hπ, hA, hQ]
  have hd' : |planeDot x y| ≤ 2 * τ := hd
  have := qcv_tail_bound c (Λ₁ := Λ₁) (Λ₂ := Λ₂) (ρ₁ := √Λ₁) (ρ₂ := √Λ₂) (p := planeSq x)
    (q := planeSq y) (d := planeDot x y) (τ := τ) (κ := κ) (B := B) hΛ₁ hΛ₂ hρ₁ hρ₂ hκ hτ hp0 hx
    hq0 hy hd' b0 b1 b2 b3 b4 b5 b6
  exact this

private theorem qcv_bigO {f : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ} {C : ℝ}
    (h : ∀ᶠ u in 𝓝 (0 : (Fin 2 → ℝ) × (Fin 2 → ℝ)), |f u| ≤ C * ‖u‖ ^ 6) :
    f =O[𝓝 0] fun u => ‖u‖ ^ 5 := by
  refine IsBigO.of_bound |C| ?_
  have h1 : ∀ᶠ u in 𝓝 (0 : (Fin 2 → ℝ) × (Fin 2 → ℝ)), ‖u‖ ≤ 1 :=
    (continuous_norm.tendsto (0 : (Fin 2 → ℝ) × (Fin 2 → ℝ))).eventually
      (ge_mem_nhds (by simp))
  filter_upwards [h, h1] with u hu hu1
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
  have h5 : 0 ≤ ‖u‖ ^ 5 := by positivity
  calc |f u| ≤ C * ‖u‖ ^ 6 := hu
    _ ≤ |C| * ‖u‖ ^ 6 := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (norm_nonneg u) 6)
    _ ≤ |C| * ‖u‖ ^ 5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg u) hu1 (by norm_num))
          (abs_nonneg C)

private theorem qcv_norm_le {Λ : ℝ} (hΛ : 0 < Λ) (x : Fin 2 → ℝ) :
    ‖(√(1 - planeSq x / (4 * Λ)) / √Λ) • x‖ ≤ 1 / √Λ * ‖x‖ := by
  have hρ : 0 < √Λ := Real.sqrt_pos.2 hΛ
  have h0 : 0 ≤ planeSq x / (4 * Λ) := by have := qcv_planeSq_nonneg x; positivity
  have h1 : √(1 - planeSq x / (4 * Λ)) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr

/-- **Square-root conversion between eccentricity vectors and canonical coordinates**
(`stepP:p8:q4-a`). Let `W` be a function of the eccentricity vectors `v = (v₁, v₂)` whose expansion
at `0` has quadratic part `A |v₁|² + A' |v₂|² + B v₁·v₂`, quartic part
`∑ c_m (quarticMonomials v₁ v₂) m` and remainder `O(‖v‖⁵)`. Composing with the exact change of
variables
`vᵢ = (1 - |uᵢ|²/(4Λᵢ))^{1/2} uᵢ/√Λᵢ` gives, up to `O(‖u‖⁵)`, the quadratic part
`A |u₁|²/Λ₁ + A' |u₂|²/Λ₂ + B u₁·u₂/√(Λ₁Λ₂)` and the quartic part `W₄(u/√Λ)` minus the correction
`A/4 |u₁|⁴/Λ₁² + A'/4 |u₂|⁴/Λ₂² + B/8 (u₁·u₂/√(Λ₁Λ₂)) (|u₁|²/Λ₁ + |u₂|²/Λ₂)`.
The overall pair prefactor `-G mᵢ mⱼ aⱼ⁻¹` is a constant factor and is left out. -/
theorem quartic_sqrt_chart_conversion {Λ₁ Λ₂ : ℝ} (h₁ : 0 < Λ₁) (h₂ : 0 < Λ₂) (A A' B : ℝ)
    (c : Fin 6 → ℝ) (W : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hW : (fun v => W v - (A * planeSq v.1 + A' * planeSq v.2 + B * planeDot v.1 v.2) -
        ∑ m, c m * quarticMonomials v.1 v.2 m) =O[𝓝 0] fun v => ‖v‖ ^ 5) :
    (fun u : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      W ((√(1 - planeSq u.1 / (4 * Λ₁)) / √Λ₁) • u.1, (√(1 - planeSq u.2 / (4 * Λ₂)) / √Λ₂) • u.2) -
        (A * (planeSq u.1 / Λ₁) + A' * (planeSq u.2 / Λ₂) +
          B * (planeDot u.1 u.2 / (√Λ₁ * √Λ₂))) -
        (∑ m, c m * quarticMonomials ((√Λ₁)⁻¹ • u.1) ((√Λ₂)⁻¹ • u.2) m -
          (A / 4 * planeSq u.1 ^ 2 / Λ₁ ^ 2 + A' / 4 * planeSq u.2 ^ 2 / Λ₂ ^ 2 +
            B / 8 * (planeDot u.1 u.2 / (√Λ₁ * √Λ₂)) *
              (planeSq u.1 / Λ₁ + planeSq u.2 / Λ₂)))) =O[𝓝 0] fun u => ‖u‖ ^ 5 := by
  have hρ₁ : 0 < √Λ₁ := Real.sqrt_pos.2 h₁
  have hρ₂ : 0 < √Λ₂ := Real.sqrt_pos.2 h₂
  set φ : (Fin 2 → ℝ) × (Fin 2 → ℝ) → (Fin 2 → ℝ) × (Fin 2 → ℝ) := fun u =>
    ((√(1 - planeSq u.1 / (4 * Λ₁)) / √Λ₁) • u.1, (√(1 - planeSq u.2 / (4 * Λ₂)) / √Λ₂) • u.2)
    with hφ
  set M : ℝ := 1 / √Λ₁ + 1 / √Λ₂ with hM
  have hM0 : 0 ≤ M := by positivity
  have hφn : ∀ u, ‖φ u‖ ≤ M * ‖u‖ := by
    intro u
    have e1 := qcv_norm_le h₁ u.1
    have e2 := qcv_norm_le h₂ u.2
    have n1 : ‖u.1‖ ≤ ‖u‖ := norm_fst_le u
    have n2 : ‖u.2‖ ≤ ‖u‖ := norm_snd_le u
    have p1 : 0 ≤ 1 / √Λ₁ := by positivity
    have p2 : 0 ≤ 1 / √Λ₂ := by positivity
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · calc _ ≤ 1 / √Λ₁ * ‖u.1‖ := e1
        _ ≤ 1 / √Λ₁ * ‖u‖ := by gcongr
        _ ≤ M * ‖u‖ := by rw [hM]; nlinarith [norm_nonneg u]
    · calc _ ≤ 1 / √Λ₂ * ‖u.2‖ := e2
        _ ≤ 1 / √Λ₂ * ‖u‖ := by gcongr
        _ ≤ M * ‖u‖ := by rw [hM]; nlinarith [norm_nonneg u]
  have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hφn ?_
    simpa using (continuous_norm.tendsto (0 : (Fin 2 → ℝ) × (Fin 2 → ℝ))).const_mul M
  have hP1 : (fun u => (fun v => W v - (A * planeSq v.1 + A' * planeSq v.2 +
      B * planeDot v.1 v.2) - ∑ m, c m * quarticMonomials v.1 v.2 m) (φ u)) =O[𝓝 0]
      fun u => ‖u‖ ^ 5 := by
    refine (hW.comp_tendsto hφ0).trans ?_
    refine IsBigO.of_bound (M ^ 5) (Eventually.of_forall fun u => ?_)
    show ‖‖φ u‖ ^ 5‖ ≤ M ^ 5 * ‖‖u‖ ^ 5‖
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 5),
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 5), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hφn u) 5
  set κ : ℝ := 1 / (2 * Λ₁) + 1 / (2 * Λ₂) with hκ
  have hev : ∀ᶠ u in 𝓝 (0 : (Fin 2 → ℝ) × (Fin 2 → ℝ)), ‖u‖ ^ 2 ≤ min Λ₁ Λ₂ / 2 :=
    ((continuous_norm.pow 2).tendsto (0 : (Fin 2 → ℝ) × (Fin 2 → ℝ))).eventually
      (ge_mem_nhds (by simpa using lt_min h₁ h₂))
  have hTail : (fun u : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      (A * planeSq (φ u).1 + A' * planeSq (φ u).2 + B * planeDot (φ u).1 (φ u).2) -
      (A * (planeSq u.1 / Λ₁) + A' * (planeSq u.2 / Λ₂) + B * (planeDot u.1 u.2 / (√Λ₁ * √Λ₂))) +
      (A / 4 * planeSq u.1 ^ 2 / Λ₁ ^ 2 + A' / 4 * planeSq u.2 ^ 2 / Λ₂ ^ 2 +
        B / 8 * (planeDot u.1 u.2 / (√Λ₁ * √Λ₂)) * (planeSq u.1 / Λ₁ + planeSq u.2 / Λ₂)) +
      (∑ m, c m * quarticMonomials (φ u).1 (φ u).2 m -
        ∑ m, c m * quarticMonomials ((√Λ₁)⁻¹ • u.1) ((√Λ₂)⁻¹ • u.2) m)) =O[𝓝 0]
      fun u => ‖u‖ ^ 5 := by
    refine qcv_bigO (C := 4 * κ ^ 2 * |B| / (√Λ₁ * √Λ₂) + κ * (12 * |c 0| / Λ₁ ^ 2 +
      12 * |c 1| / Λ₂ ^ 2 + 8 * |c 2| / (Λ₁ * Λ₂) + 8 * |c 3| / (Λ₁ * Λ₂) +
      12 * |c 4| / (Λ₁ * (√Λ₁ * √Λ₂)) + 12 * |c 5| / (Λ₂ * (√Λ₁ * √Λ₂)))) ?_
    filter_upwards [hev] with u hu
    have n1 : ‖u.1‖ ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le u) 2
    have n2 : ‖u.2‖ ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le u) 2
    have hm1 : min Λ₁ Λ₂ ≤ Λ₁ := min_le_left _ _
    have hm2 : min Λ₁ Λ₂ ≤ Λ₂ := min_le_right _ _
    have hd : |planeDot u.1 u.2| ≤ 2 * ‖u‖ ^ 2 := by
      refine (qcv_abs_planeDot_le _ _).trans ?_
      have := norm_fst_le u
      have := norm_snd_le u
      nlinarith [norm_nonneg u.1, norm_nonneg u.2, norm_nonneg u]
    have := qcv_tail_pt c A A' B (κ := κ) (τ := ‖u‖ ^ 2) u.1 u.2 h₁ h₂ (by positivity)
      (by rw [hκ]; have : 0 < 1 / (2 * Λ₂) := by positivity
          linarith)
      (by rw [hκ]; have : 0 < 1 / (2 * Λ₁) := by positivity
          linarith)
      ((qcv_planeSq_le _).trans (by linarith)) ((qcv_planeSq_le _).trans (by linarith))
      (by linarith) (by linarith) hd
    rw [← pow_mul] at this
    exact this
  refine (hP1.add hTail).congr_left (fun u => ?_)
  simp only [hφ]
  ring

/-- **Square-root conversion with a constant term** (`stepP:p8:q4-a`). The same statement as
`quartic_sqrt_chart_conversion` for a function `W` whose expansion at `0` is
`W(0) + W₂ + W₄ + O(‖v‖⁵)`, where `W₂ = A |v₁|² + A' |v₂|² + B v₁·v₂` is the quadratic part and
`W₄ = ∑ c_m (quarticMonomials v₁ v₂) m` the quartic part; the constant term `W(0)` is carried
through, and the overall pair prefactor `pref` (`-G mᵢ mⱼ aⱼ⁻¹` in the source) multiplies the whole
expansion. -/
theorem quartic_sqrt_chart_conversion_const {Λ₁ Λ₂ : ℝ} (h₁ : 0 < Λ₁) (h₂ : 0 < Λ₂)
    (A A' B W0 pref : ℝ) (c : Fin 6 → ℝ) (W : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hW : (fun v => W v - W0 - (A * planeSq v.1 + A' * planeSq v.2 + B * planeDot v.1 v.2) -
        ∑ m, c m * quarticMonomials v.1 v.2 m) =O[𝓝 0] fun v => ‖v‖ ^ 5) :
    (fun u : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      pref * (W ((√(1 - planeSq u.1 / (4 * Λ₁)) / √Λ₁) • u.1,
          (√(1 - planeSq u.2 / (4 * Λ₂)) / √Λ₂) • u.2) - W0 -
        (A * (planeSq u.1 / Λ₁) + A' * (planeSq u.2 / Λ₂) +
          B * (planeDot u.1 u.2 / (√Λ₁ * √Λ₂))) -
        (∑ m, c m * quarticMonomials ((√Λ₁)⁻¹ • u.1) ((√Λ₂)⁻¹ • u.2) m -
          (A / 4 * planeSq u.1 ^ 2 / Λ₁ ^ 2 + A' / 4 * planeSq u.2 ^ 2 / Λ₂ ^ 2 +
            B / 8 * (planeDot u.1 u.2 / (√Λ₁ * √Λ₂)) *
              (planeSq u.1 / Λ₁ + planeSq u.2 / Λ₂))))) =O[𝓝 0] fun u => ‖u‖ ^ 5 := by
  have h := quartic_sqrt_chart_conversion h₁ h₂ A A' B c (fun v => W v - W0)
    (by simpa only [sub_sub] using hW)
  refine (h.const_mul_left pref).congr_left (fun u => ?_)
  simp only [sub_sub]

end SecularForm
end KAM.Planetary
end
