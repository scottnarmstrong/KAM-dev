/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The `λ`-arithmetic of `X_+` (blueprint-W `bpW:w5:step` (ii), steps `st-1`, `st-2`)

`stepXplus_arith`: with `ε₀ + λε₁ ≤ ε`, `M₀ + λM₁ ≤ M_F`, `16 M_F ≤ ση²`:
`S + λ D ≤ 896 η ε + 168 ε M_F/(σ η²)`, where `S`, `D` are the sup and Lipschitz constants of the
two-parameter bound of `X_+` (pull-back of `X_P - X_R` and commutator integral).
-/

@[expose] public section

namespace KAM.Wave

theorem stepXplus_arith {ε₀ ε₁ ε lam M₀ M₁ MF η σ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hε₀ : 0 ≤ ε₀)
    (hε₁ : 0 ≤ ε₁) (hlam : 0 ≤ lam) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hε : ε₀ + lam * ε₁ ≤ ε)
    (hM : M₀ + lam * M₁ ≤ MF) (hs : 16 * MF ≤ σ * η ^ 2) :
    (2 * (128 * η * ε₀) + 2 * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ))) +
      lam * ((2 * (128 * η * ε₁ + 2 * (128 * η * ε₀) / σ * (η⁻¹ ^ 2 * (2 * M₁))) +
          4 * (η⁻¹ ^ 2 * (2 * M₁ / (σ / 8))) * (128 * η * ε₀)) +
        (2 * (η⁻¹ ^ 2 * (8 * (M₀ * (3 * ε₁) + 3 * ε₀ * M₁) / σ) +
          2 * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ)) / σ * (η⁻¹ ^ 2 * (2 * M₁))) +
        4 * (η⁻¹ ^ 2 * (2 * M₁ / (σ / 8))) * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ)))) ≤
      896 * η * ε + 168 * ε * MF / (σ * η ^ 2) := by
  have hσ2 : 0 < σ * η ^ 2 := by positivity
  set q₀ : ℝ := M₀ / (σ * η ^ 2) with hq₀
  set k : ℝ := η⁻¹ ^ 2 * lam * M₁ / σ with hk
  set Q : ℝ := MF / (σ * η ^ 2) with hQ
  have hq₀0 : 0 ≤ q₀ := by positivity
  have hk0 : 0 ≤ k := by positivity
  have hQ16 : Q ≤ 1 / 16 := by rw [hQ, div_le_iff₀ hσ2]; linarith
  have hqk : q₀ + k ≤ Q := by
    have : q₀ + k = (M₀ + lam * M₁) / (σ * η ^ 2) := by rw [hq₀, hk]; field_simp
    rw [this, hQ]; exact div_le_div_of_nonneg_right hM hσ2.le
  have key : (2 * (128 * η * ε₀) + 2 * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ))) +
      lam * ((2 * (128 * η * ε₁ + 2 * (128 * η * ε₀) / σ * (η⁻¹ ^ 2 * (2 * M₁))) +
          4 * (η⁻¹ ^ 2 * (2 * M₁ / (σ / 8))) * (128 * η * ε₀)) +
        (2 * (η⁻¹ ^ 2 * (8 * (M₀ * (3 * ε₁) + 3 * ε₀ * M₁) / σ) +
          2 * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ)) / σ * (η⁻¹ ^ 2 * (2 * M₁))) +
        4 * (η⁻¹ ^ 2 * (2 * M₁ / (σ / 8))) * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ)))) =
      256 * η * ε₀ + 48 * ε₀ * q₀ + 256 * η * lam * ε₁ + 9216 * η * ε₀ * k +
        48 * ε₁ * lam * q₀ + 48 * ε₀ * k + 1728 * ε₀ * q₀ * k := by
    rw [hq₀, hk]; field_simp; ring
  rw [key]
  have hQ' : 168 * ε * MF / (σ * η ^ 2) = 168 * ε * Q := by rw [hQ]; ring
  rw [hQ']
  clear_value q₀ k Q
  have hε' := hε
  have hε0le : ε₀ ≤ ε := by nlinarith [mul_nonneg hlam hε₁]
  have hq0k : q₀ * k ≤ Q / 64 := by nlinarith [sq_nonneg (q₀ - k)]
  have hkQ : k ≤ Q := by linarith
  have hq0Q : q₀ ≤ Q := by linarith
  have hη0 : 0 ≤ η := hη.le
  have h1 : 9216 * η * ε₀ * k ≤ 576 * η * ε₀ := by
    have : k ≤ 1 / 16 := by linarith
    nlinarith [mul_nonneg hη0 hε₀]
  have h2 : 48 * ε₀ * q₀ + 48 * ε₁ * lam * q₀ ≤ 48 * ε * q₀ := by
    nlinarith [mul_nonneg hlam hε₁]
  have h3 : 48 * ε₀ * k ≤ 48 * ε * k := by nlinarith
  have h4 : 1728 * ε₀ * q₀ * k ≤ 27 * ε * Q := by
    have : ε₀ * (q₀ * k) ≤ ε * (Q / 64) :=
      mul_le_mul hε0le hq0k (by positivity) (by linarith)
    linarith
  have hε0 : 0 ≤ ε := by linarith
  have h5 : 48 * ε * q₀ + 48 * ε * k ≤ 48 * ε * Q := by
    have := mul_le_mul_of_nonneg_left hqk hε0
    linarith
  have h6 : 256 * η * (ε₀ + lam * ε₁) ≤ 256 * η * ε :=
    mul_le_mul_of_nonneg_left hε' (by positivity)
  have h7 : 576 * η * ε₀ ≤ 576 * η * ε := by
    have := mul_le_mul_of_nonneg_left hε0le (by positivity : (0 : ℝ) ≤ 576 * η)
    linarith
  have h8 : 27 * ε * Q ≤ 168 * ε * Q := by
    have := mul_nonneg hε0 (by linarith : 0 ≤ Q)
    linarith
  have h9 : 0 ≤ η * ε := mul_nonneg hη0 hε0
  linarith

end KAM.Wave
