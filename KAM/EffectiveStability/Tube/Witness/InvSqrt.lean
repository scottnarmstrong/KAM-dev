/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Witness.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Inverse-square-root witnesses in the `C¹` sup sense (T2-CONF, N4)

Given a square-root model `C1Close (fun φ => √(B φ)) W e₀ e₁` (`Witness/Sqrt.lean`), a witness
`Y ≈ 1/√B` is certified by its residual `E = 1 - W Y`, computed exactly. With `s = √B`:

  `1/s - Y = N / s`,  `N = 1 - Y s = E - (s - W) Y`,

so `|1/s - Y| ≤ (q + e₀ Y₀) / σ₀` when `|E| ≤ q`, `|Y| ≤ Y₀` and `s ≥ σ₀`. For the derivatives,
`∂(N/s) = ∂N / s - N ∂s / s²` with `∂N = ∂E - (∂s - ∂W) Y - (s - W) ∂Y`, `|∂s| ≤ ω₁ + e₁`:

  `|∂_a(1/s - Y)| ≤ (q' + e₁ Y₀ + e₀ Y₁) / σ₀ + (q + e₀ Y₀)(ω₁ + e₁) / σ₀²`.

* `invSqrtErr₀`, `invSqrtErr₁`: the error bounds;
* `C1Close.invSqrt_witness`: `C1Close (fun φ => 1 / √(B φ)) Y d₀ d₁`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- The value error of an inverse-square-root witness: `(q + e₀ Y₀) / σ₀`. -/
noncomputable def invSqrtErr₀ (σ₀ e₀ q Y₀ : ℝ) : ℝ := (q + e₀ * Y₀) / σ₀

/-- The derivative error of an inverse-square-root witness:
`(q' + e₁ Y₀ + e₀ Y₁) / σ₀ + (q + e₀ Y₀)(ω₁ + e₁) / σ₀²`. -/
noncomputable def invSqrtErr₁ (σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁ : ℝ) : ℝ :=
  (q' + e₁ * Y₀ + e₀ * Y₁) / σ₀ + (q + e₀ * Y₀) * (ω₁ + e₁) / σ₀ ^ 2

/-- The partial derivative of `1 / s` where `s ≠ 0`. -/
theorem pderiv_one_div {s : (Fin 2 → ℝ) → ℝ} {φ : Fin 2 → ℝ} (hs : DifferentiableAt ℝ s φ)
    (hne : s φ ≠ 0) (a : Fin 2) :
    pderiv (fun φ => 1 / s φ) φ a = -pderiv s φ a / s φ ^ 2 := by
  simp only [pderiv, one_div]
  have h : HasFDerivAt (fun φ => (s φ)⁻¹) _ φ :=
    (hasDerivAt_inv (𝕜 := ℝ) hne).comp_hasFDerivAt φ hs.hasFDerivAt
  rw [h.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  simp [div_eq_mul_inv, mul_comm]

/-- The partial derivative of `1 - W * Y`. -/
theorem pderiv_one_sub_mul {W Y : (Fin 2 → ℝ) → ℝ} {φ : Fin 2 → ℝ}
    (hW : DifferentiableAt ℝ W φ) (hY : DifferentiableAt ℝ Y φ) (a : Fin 2) :
    pderiv (fun φ => 1 - W φ * Y φ) φ a = -(W φ * pderiv Y φ a + Y φ * pderiv W φ a) := by
  simp only [pderiv]
  have h : HasFDerivAt (fun φ => 1 - W φ * Y φ) _ φ :=
    (hasFDerivAt_const (1 : ℝ) φ).sub (hW.hasFDerivAt.mul hY.hasFDerivAt)
  rw [h.fderiv]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    _root_.zero_apply]
  ring

/-- **Inverse-square-root witness.** From the square-root model `C1Close √B W e₀ e₁`, `B ≥ σ₀² > 0`,
`|∂_a W| ≤ ω₁`, and a differentiable `Y` with `|1 - W Y| ≤ q`, `|∂_a(1 - W Y)| ≤ q'`, `|Y| ≤ Y₀`,
`|∂_a Y| ≤ Y₁`: `1/√B` is `C¹`-close to `Y` with errors `invSqrtErr₀`, `invSqrtErr₁`. -/
theorem C1Close.invSqrt_witness {B W Y : (Fin 2 → ℝ) → ℝ} {σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁ : ℝ}
    (H : C1Close (fun φ => √(B φ)) W e₀ e₁) (hσ : 0 < σ₀) (hB : ∀ φ, σ₀ ^ 2 ≤ B φ)
    (hω : ∀ φ a, |pderiv W φ a| ≤ ω₁) (hYd : Differentiable ℝ Y)
    (hq : ∀ φ, |1 - W φ * Y φ| ≤ q) (hq' : ∀ φ a, |pderiv (fun φ => 1 - W φ * Y φ) φ a| ≤ q')
    (hY₀ : ∀ φ, |Y φ| ≤ Y₀) (hY₁ : ∀ φ a, |pderiv Y φ a| ≤ Y₁) :
    C1Close (fun φ => 1 / √(B φ)) Y (invSqrtErr₀ σ₀ e₀ q Y₀)
      (invSqrtErr₁ σ₀ e₀ e₁ ω₁ q q' Y₀ Y₁) := by
  set s : (Fin 2 → ℝ) → ℝ := fun φ => √(B φ) with hs_def
  have hsd : Differentiable ℝ s := H.differentiable_left
  have hWd : Differentiable ℝ W := H.differentiable_right
  have hs : ∀ φ, σ₀ ≤ s φ := fun φ => le_sqrt_of_sq_le hσ.le (hB φ)
  have hspos : ∀ φ, 0 < s φ := fun φ => hσ.trans_le (hs φ)
  have he₀ : 0 ≤ e₀ := H.e₀_nonneg
  have he₁ : 0 ≤ e₁ := H.e₁_nonneg
  -- `N = 1 - Y s = E - (s - W) Y` and its bound
  have hN : ∀ φ, |1 - Y φ * s φ| ≤ q + e₀ * Y₀ := by
    intro φ
    have hid : 1 - Y φ * s φ = (1 - W φ * Y φ) - (s φ - W φ) * Y φ := by ring
    rw [hid]
    have h1 := abs_sub (1 - W φ * Y φ) ((s φ - W φ) * Y φ)
    have h2 : |(s φ - W φ) * Y φ| ≤ e₀ * Y₀ := by
      rw [abs_mul]
      exact mul_le_mul (H.abs_sub_le φ) (hY₀ φ) (abs_nonneg _) he₀
    linarith [hq φ]
  have hdiv : Differentiable ℝ (fun φ => 1 / s φ) :=
    fun φ => by simpa only [one_div] using (hsd φ).fun_inv (hspos φ).ne'
  refine C1Close.intro hdiv hYd (fun φ => ?_) fun φ a => ?_
  · have hid : 1 / s φ - Y φ = (1 - Y φ * s φ) / s φ := by
      field_simp [(hspos φ).ne']
    show |1 / s φ - Y φ| ≤ _
    rw [hid, abs_div, abs_of_pos (hspos φ), invSqrtErr₀]
    exact div_le_div₀ ((abs_nonneg _).trans (hN φ)) (hN φ) hσ (hs φ)
  · show |pderiv (fun φ => 1 / s φ) φ a - pderiv Y φ a| ≤ _
    rw [pderiv_one_div (hsd φ) (hspos φ).ne' a]
    have hE' := hq' φ a
    rw [pderiv_one_sub_mul (hWd φ) (hYd φ) a] at hE'
    set S := s φ
    set dS := pderiv s φ a
    set dW := pderiv W φ a
    set dY := pderiv Y φ a
    have hSpos : 0 < S := hspos φ
    have hσS : σ₀ ≤ S := hs φ
    -- `∂N = ∂E - (∂s - ∂W) Y - (s - W) ∂Y`
    set dN := -(W φ * dY + Y φ * dW) - (dS - dW) * Y φ - (S - W φ) * dY with hdN
    set N := 1 - Y φ * S with hNdef
    have hid : -dS / S ^ 2 - dY = dN / S - N * dS / S ^ 2 := by
      rw [hdN, hNdef]
      field_simp
      ring
    rw [hid, invSqrtErr₁]
    have hdNb : |dN| ≤ q' + e₁ * Y₀ + e₀ * Y₁ := by
      have h1 : |(dS - dW) * Y φ| ≤ e₁ * Y₀ := by
        rw [abs_mul]
        exact mul_le_mul (H.abs_pderiv_sub_le φ a) (hY₀ φ) (abs_nonneg _) he₁
      have h2 : |(S - W φ) * dY| ≤ e₀ * Y₁ := by
        rw [abs_mul]
        exact mul_le_mul (H.abs_sub_le φ) (hY₁ φ a) (abs_nonneg _) he₀
      have h3 := abs_sub (-(W φ * dY + Y φ * dW) - (dS - dW) * Y φ) ((S - W φ) * dY)
      have h4 := abs_sub (-(W φ * dY + Y φ * dW)) ((dS - dW) * Y φ)
      linarith
    have hdSb : |dS| ≤ ω₁ + e₁ := by
      have := abs_add_le (dS - dW) dW
      rw [sub_add_cancel] at this
      linarith [H.abs_pderiv_sub_le φ a, hω φ a]
    have hNb : |N| ≤ q + e₀ * Y₀ := hN φ
    have t1 : |dN / S| ≤ (q' + e₁ * Y₀ + e₀ * Y₁) / σ₀ := by
      rw [abs_div, abs_of_pos hSpos]
      exact div_le_div₀ ((abs_nonneg _).trans hdNb) hdNb hσ hσS
    have t2 : |N * dS / S ^ 2| ≤ (q + e₀ * Y₀) * (ω₁ + e₁) / σ₀ ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos (pow_pos hSpos 2)]
      exact div_le_div₀ (mul_nonneg ((abs_nonneg _).trans hNb) ((abs_nonneg _).trans hdSb))
        (mul_le_mul hNb hdSb (abs_nonneg _) ((abs_nonneg _).trans hNb)) (pow_pos hσ 2)
        (pow_le_pow_left₀ hσ.le hσS 2)
    exact (abs_sub _ _).trans (add_le_add t1 t2)

end KAM.EffectiveStability.Tube

end
