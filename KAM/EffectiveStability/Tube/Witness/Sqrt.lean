/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Algebra.C1
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-root witnesses in the `C¹` sup sense (T2-CONF, N4)

The tube checker models `√B` for a positive function `B` of the reduced angles (in practice a
trigonometric polynomial, the shifted action `B₀(φ)`) by a witness `W ≈ √B` whose residual
`D = B - W²` is computed exactly. The identity

  `√B - W = (B - W²) / (√B + W)`

turns a bound `|D| ≤ ρ` into `|√B - W| ≤ ρ / (σ₀ + w₀)`, where `σ₀ ≤ √B` and `w₀ ≤ W`. For the
derivatives, `∂D = ∂B - 2 W ∂W` gives

  `∂√B - ∂W = ∂B / (2√B) - ∂W = (∂D - 2 (√B - W) ∂W) / (2√B)`,

so `|∂_a(√B - W)| ≤ (ρ' + 2 e₀ ω₁) / (2 σ₀)` with `|∂_a D| ≤ ρ'`, `|∂_a W| ≤ ω₁`.

The lower bound of `B` is given as `σ₀² ≤ B` with `σ₀ > 0`, so that every error bound is a rational
expression in the data (no square root of a bound is ever needed).

* `sqrtErr₀`, `sqrtErr₁`: the error bounds;
* `C1Close.sqrt_witness`: `C1Close (fun φ => √(B φ)) W (sqrtErr₀ σ₀ w₀ ρ) (sqrtErr₁ σ₀ w₀ ρ ρ' ω₁)`;
* `pderiv_sqrt`: the partial derivative of `√B`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- The value error of a square-root witness: `ρ / (σ₀ + w₀)`. -/
noncomputable def sqrtErr₀ (σ₀ w₀ ρ : ℝ) : ℝ := ρ / (σ₀ + w₀)

/-- The derivative error of a square-root witness: `(ρ' + 2 e₀ ω₁) / (2 σ₀)`, `e₀ = sqrtErr₀`. -/
noncomputable def sqrtErr₁ (σ₀ w₀ ρ ρ' ω₁ : ℝ) : ℝ := (ρ' + 2 * sqrtErr₀ σ₀ w₀ ρ * ω₁) / (2 * σ₀)

/-- The partial derivative of `√B` where `B > 0`: `∂_a √B = ∂_a B / (2 √B)`. -/
theorem pderiv_sqrt {B : (Fin 2 → ℝ) → ℝ} {φ : Fin 2 → ℝ} (hB : DifferentiableAt ℝ B φ)
    (hpos : B φ ≠ 0) (a : Fin 2) :
    pderiv (fun φ => √(B φ)) φ a = pderiv B φ a / (2 * √(B φ)) := by
  simp only [pderiv]
  rw [(hB.hasFDerivAt.sqrt hpos).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/-- The partial derivative of `B - W * W`. -/
theorem pderiv_sub_mul_self {B W : (Fin 2 → ℝ) → ℝ} {φ : Fin 2 → ℝ}
    (hB : DifferentiableAt ℝ B φ) (hW : DifferentiableAt ℝ W φ) (a : Fin 2) :
    pderiv (fun φ => B φ - W φ * W φ) φ a = pderiv B φ a - 2 * W φ * pderiv W φ a := by
  simp only [pderiv]
  have h : HasFDerivAt (fun φ => B φ - W φ * W φ) _ φ :=
    hB.hasFDerivAt.sub (hW.hasFDerivAt.mul hW.hasFDerivAt)
  rw [h.fderiv]
  simp only [_root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

/-- `√B ≥ σ₀` from `σ₀² ≤ B` and `σ₀ ≥ 0`. -/
theorem le_sqrt_of_sq_le {σ₀ b : ℝ} (hσ : 0 ≤ σ₀) (h : σ₀ ^ 2 ≤ b) : σ₀ ≤ √b :=
  calc σ₀ = √(σ₀ ^ 2) := (Real.sqrt_sq hσ).symm
    _ ≤ √b := Real.sqrt_le_sqrt h

/-- **Square-root witness.** If `B ≥ σ₀² > 0`, `W ≥ w₀ ≥ 0`, `|B - W²| ≤ ρ`,
`|∂_a(B - W²)| ≤ ρ'` and `|∂_a W| ≤ ω₁`, then `√B` is `C¹`-close to `W` with errors
`ρ / (σ₀ + w₀)` and `(ρ' + 2 e₀ ω₁) / (2 σ₀)`. -/
theorem C1Close.sqrt_witness {B W : (Fin 2 → ℝ) → ℝ} {σ₀ w₀ ρ ρ' ω₁ : ℝ}
    (hBd : Differentiable ℝ B) (hWd : Differentiable ℝ W) (hσ : 0 < σ₀)
    (hB : ∀ φ, σ₀ ^ 2 ≤ B φ) (hw₀ : 0 ≤ w₀) (hW : ∀ φ, w₀ ≤ W φ)
    (hρ : ∀ φ, |B φ - W φ * W φ| ≤ ρ)
    (hρ' : ∀ φ a, |pderiv (fun φ => B φ - W φ * W φ) φ a| ≤ ρ')
    (hω : ∀ φ a, |pderiv W φ a| ≤ ω₁) :
    C1Close (fun φ => √(B φ)) W (sqrtErr₀ σ₀ w₀ ρ) (sqrtErr₁ σ₀ w₀ ρ ρ' ω₁) := by
  have hBpos : ∀ φ, 0 < B φ := fun φ => (pow_pos hσ 2).trans_le (hB φ)
  have hs : ∀ φ, σ₀ ≤ √(B φ) := fun φ => le_sqrt_of_sq_le hσ.le (hB φ)
  have hsW : ∀ φ, 0 < √(B φ) + W φ := fun φ => by linarith [hs φ, hW φ]
  -- the value bound
  have h0 : ∀ φ, |√(B φ) - W φ| ≤ sqrtErr₀ σ₀ w₀ ρ := by
    intro φ
    have hid : √(B φ) - W φ = (B φ - W φ * W φ) / (√(B φ) + W φ) := by
      rw [eq_div_iff (hsW φ).ne', ← Real.mul_self_sqrt (hBpos φ).le]
      simp only [Real.sqrt_mul_self (Real.sqrt_nonneg _)]
      ring
    rw [hid, abs_div, abs_of_pos (hsW φ), sqrtErr₀]
    exact div_le_div₀ ((abs_nonneg _).trans (hρ φ)) (hρ φ) (by linarith) (by linarith [hs φ, hW φ])
  refine C1Close.intro (hBd.sqrt fun φ => (hBpos φ).ne') hWd h0 fun φ a => ?_
  rw [pderiv_sqrt (hBd φ) (hBpos φ).ne' a]
  have hD := hρ' φ a
  rw [pderiv_sub_mul_self (hBd φ) (hWd φ) a] at hD
  set s := √(B φ)
  set dB := pderiv B φ a
  set dW := pderiv W φ a
  have hspos : 0 < s := hσ.trans_le (hs φ)
  have hid : dB / (2 * s) - dW = ((dB - 2 * W φ * dW) - 2 * (s - W φ) * dW) / (2 * s) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * s), sqrtErr₁]
  have he₀ := h0 φ
  have hω' := hω φ a
  have hnum : |(dB - 2 * W φ * dW) - 2 * (s - W φ) * dW| ≤ ρ' + 2 * sqrtErr₀ σ₀ w₀ ρ * ω₁ := by
    have h1 := abs_sub (dB - 2 * W φ * dW) (2 * (s - W φ) * dW)
    have h2 : |2 * (s - W φ) * dW| ≤ 2 * sqrtErr₀ σ₀ w₀ ρ * ω₁ := by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul he₀ hω' (abs_nonneg _) ((abs_nonneg _).trans he₀)
      linarith
    linarith
  exact div_le_div₀ ((abs_nonneg _).trans hnum) hnum (by positivity) (by linarith [hs φ])

end KAM.EffectiveStability.Tube

end
