/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Scalar error bounds for products (T2-CONF, N3)

The pointwise inequalities behind every product rule of the tube checker: with
`|f - p| ≤ e₀`, `|g - q| ≤ d₀` and `|p| ≤ P₀`, `|q| ≤ Q₀`,
* `abs_mul_sub_mul_le`: `|f g - p q| ≤ P₀ d₀ + Q₀ e₀ + e₀ d₀`;
* `abs_leibniz_sub_le`: for derivatives `F, G, P, Q` of `f, g, p, q` in one direction, with
  `|F - P| ≤ e₁`, `|G - Q| ≤ d₁`, `|P| ≤ P₁`, `|Q| ≤ Q₁`,
  `|(f G + g F) - (p Q + q P)| ≤ P₁ d₀ + P₀ d₁ + Q₁ e₀ + Q₀ e₁ + e₁ d₀ + e₀ d₁`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

theorem abs_mul_le_of_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- The value bound of a product. -/
theorem abs_mul_sub_mul_le {f g p q e₀ d₀ P₀ Q₀ : ℝ} (he : |f - p| ≤ e₀) (hd : |g - q| ≤ d₀)
    (hP : |p| ≤ P₀) (hQ : |q| ≤ Q₀) : |f * g - p * q| ≤ P₀ * d₀ + Q₀ * e₀ + e₀ * d₀ := by
  rw [show f * g - p * q = p * (g - q) + q * (f - p) + (f - p) * (g - q) by ring]
  have h1 := abs_mul_le_of_le hP hd
  have h2 := abs_mul_le_of_le hQ he
  have h3 := abs_mul_le_of_le he hd
  have a1 := abs_add_le (p * (g - q)) (q * (f - p))
  have a2 := abs_add_le (p * (g - q) + q * (f - p)) ((f - p) * (g - q))
  linarith

/-- The derivative bound of a product (Leibniz rule). -/
theorem abs_leibniz_sub_le {f g p q F G P Q e₀ d₀ e₁ d₁ P₀ Q₀ P₁ Q₁ : ℝ}
    (he₀ : |f - p| ≤ e₀) (hd₀ : |g - q| ≤ d₀) (he₁ : |F - P| ≤ e₁) (hd₁ : |G - Q| ≤ d₁)
    (hP₀ : |p| ≤ P₀) (hQ₀ : |q| ≤ Q₀) (hP₁ : |P| ≤ P₁) (hQ₁ : |Q| ≤ Q₁) :
    |(f * G + g * F) - (p * Q + q * P)| ≤
      P₁ * d₀ + P₀ * d₁ + Q₁ * e₀ + Q₀ * e₁ + e₁ * d₀ + e₀ * d₁ := by
  rw [show (f * G + g * F) - (p * Q + q * P) =
    (g - q) * P + p * (G - Q) + (f - p) * Q + q * (F - P) + (F - P) * (g - q) +
      (f - p) * (G - Q) by ring]
  have t1 := abs_mul_le_of_le hd₀ hP₁
  have t2 := abs_mul_le_of_le hP₀ hd₁
  have t3 := abs_mul_le_of_le he₀ hQ₁
  have t4 := abs_mul_le_of_le hQ₀ he₁
  have t5 := abs_mul_le_of_le he₁ hd₀
  have t6 := abs_mul_le_of_le he₀ hd₁
  have a1 := abs_add_le ((g - q) * P) (p * (G - Q))
  have a2 := abs_add_le ((g - q) * P + p * (G - Q)) ((f - p) * Q)
  have a3 := abs_add_le ((g - q) * P + p * (G - Q) + (f - p) * Q) (q * (F - P))
  have a4 := abs_add_le ((g - q) * P + p * (G - Q) + (f - p) * Q + q * (F - P))
    ((F - P) * (g - q))
  have a5 := abs_add_le ((g - q) * P + p * (G - Q) + (f - p) * Q + q * (F - P) +
    (F - P) * (g - q)) ((f - p) * (G - Q))
  linarith

/-- `|x + y - (a + b)| ≤ e + d` from `|x - a| ≤ e`, `|y - b| ≤ d`. -/
theorem abs_add_sub_add_le {x y a b e d : ℝ} (h1 : |x - a| ≤ e) (h2 : |y - b| ≤ d) :
    |x + y - (a + b)| ≤ e + d := by
  rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- `|x - y - (a - b)| ≤ e + d` from `|x - a| ≤ e`, `|y - b| ≤ d`. -/
theorem abs_sub_sub_sub_le {x y a b e d : ℝ} (h1 : |x - a| ≤ e) (h2 : |y - b| ≤ d) :
    |x - y - (a - b)| ≤ e + d := by
  rw [show x - y - (a - b) = (x - a) + -(y - b) by ring]
  exact (abs_add_le _ _).trans (add_le_add h1 (by rw [abs_neg]; exact h2))

/-- The triangle inequality through a middle point. -/
theorem abs_sub_le_of_le {x y z e d : ℝ} (h1 : |x - y| ≤ e) (h2 : |y - z| ≤ d) :
    |x - z| ≤ e + d := by
  have := abs_add_le (x - y) (y - z)
  rw [sub_add_sub_cancel] at this
  linarith

/-- A bound through a model: `|x| ≤ P + e` from `|x - p| ≤ e`, `|p| ≤ P`. -/
theorem abs_le_of_sub_le {x p e P : ℝ} (h : |x - p| ≤ e) (hp : |p| ≤ P) : |x| ≤ P + e := by
  have := abs_add_le (x - p) p
  rw [sub_add_cancel] at this
  linarith

end KAM.EffectiveStability.Tube

end
