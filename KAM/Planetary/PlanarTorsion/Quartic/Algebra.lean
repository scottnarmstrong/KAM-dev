/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Planar quartic torsion: the exact conversion remainder (P11C, package T6)

Blueprint P, Part 11b (`stepP:p11b:qe-conv`).  With `a_i = |u_i|²/I_i`, `d = u₁·u₂/√(I₁I₂)` and
`σ = √((1 - a₁/4)(1 - a₂/4))`, the squared lengths of the eccentricity vectors are exactly
`a_i - a_i²/4`, their scalar product is `d σ`, and the degree-four part of the pair jet in `u`
is the displayed quartic.  `qe_alg` bounds the difference between the pair jet at the eccentricity
vector and its polynomial part (degree `≤ 4` in `u`) by the sixth power of `‖u‖`.
-/

@[expose] public noncomputable section
namespace KAM.Planetary

/-- The pair jet evaluated at the eccentricity vector, in the variables `(a₁, a₂, d, σ)`
(constant term removed). -/
def qeJetExpr (co : Fin 8 → ℝ) (a0 a1 d σ : ℝ) : ℝ :=
  co 0 * ((a0 - a0 ^ 2 / 4) + (a1 - a1 ^ 2 / 4)) + co 1 * (d * σ) +
    co 2 * (a0 - a0 ^ 2 / 4) ^ 2 + co 3 * (a1 - a1 ^ 2 / 4) ^ 2 +
    co 4 * ((a0 - a0 ^ 2 / 4) * (a1 - a1 ^ 2 / 4)) + co 5 * (d * σ) ^ 2 +
    co 6 * ((a0 - a0 ^ 2 / 4) * (d * σ)) + co 7 * ((a1 - a1 ^ 2 / 4) * (d * σ))

/-- The polynomial part of `qeJetExpr` of degree at most four in `u`. -/
def qePolyExpr (co : Fin 8 → ℝ) (a0 a1 d : ℝ) : ℝ :=
  co 0 * (a0 + a1) + co 1 * d + (co 2 - co 0 / 4) * a0 ^ 2 + (co 3 - co 0 / 4) * a1 ^ 2 +
    co 4 * (a0 * a1) + co 5 * d ^ 2 + (co 6 - co 1 / 8) * (a0 * d) +
    (co 7 - co 1 / 8) * (a1 * d)

theorem qe_alg (co : Fin 8 → ℝ) (a0 a1 d σ : ℝ) (h0 : 0 ≤ a0) (h1 : 0 ≤ a1)
    (hm : a0 + a1 ≤ 1) (hd : d ^ 2 ≤ a0 * a1) (hσ0 : 0 ≤ σ)
    (hσ : σ ^ 2 = (1 - a0 / 4) * (1 - a1 / 4)) :
    |qeJetExpr co a0 a1 d σ - qePolyExpr co a0 a1 d| ≤ (∑ i, |co i|) * (a0 + a1) ^ 3 := by
  set m := a0 + a1 with hmdef
  have hm0 : 0 ≤ m := by positivity
  have ha0m : a0 ≤ m := by linarith
  have ha1m : a1 ≤ m := by linarith
  have hprod : a0 * a1 ≤ m ^ 2 / 4 := by nlinarith [sq_nonneg (a0 - a1)]
  have hd1 : |d| ≤ m / 2 := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    nlinarith
  have hσ1 : σ ≤ 1 := by nlinarith [mul_nonneg h0 h1]
  have hσ2 : 1 - m / 4 ≤ σ := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg h0 h1]
  have hmsq : m ^ 2 ≤ m := by nlinarith
  have hm3 : 0 ≤ m ^ 3 := by positivity
  have hp0 : 0 ≤ a0 * a1 := mul_nonneg h0 h1
  have hσsq : σ ^ 2 - 1 = -m / 4 + a0 * a1 / 16 := by rw [hσ, hmdef]; ring
  have hq : |-m / 4 + a0 * a1 / 16| ≤ m := by
    rw [abs_le]; constructor <;> linarith
  -- the defect of the square root
  set ε := σ - 1 + m / 8 with hε
  have hεeq : ε * (1 + σ - m / 8) = a0 * a1 / 16 - m ^ 2 / 64 := by
    have : σ ^ 2 = 1 - m / 4 + a0 * a1 / 16 := by linarith
    rw [hε]; nlinarith
  have hεb : |ε| ≤ m ^ 2 / 16 := by
    have hpos : 7 / 8 ≤ 1 + σ - m / 8 := by linarith
    have hδ : |a0 * a1 / 16 - m ^ 2 / 64| ≤ m ^ 2 / 64 := by
      rw [abs_le]; constructor <;> linarith
    have : |ε| * (7 / 8) ≤ m ^ 2 / 64 := by
      calc |ε| * (7 / 8) ≤ |ε| * (1 + σ - m / 8) :=
            mul_le_mul_of_nonneg_left hpos (abs_nonneg _)
        _ = |ε * (1 + σ - m / 8)| := by
            rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 + σ - m / 8 by linarith)]
        _ = |a0 * a1 / 16 - m ^ 2 / 64| := by rw [hεeq]
        _ ≤ m ^ 2 / 64 := hδ
    nlinarith [sq_nonneg m]
  -- the individual pieces
  have e1 : |d * ε| ≤ m ^ 3 := by
    rw [abs_mul]
    have : |d| * |ε| ≤ m / 2 * (m ^ 2 / 16) :=
      mul_le_mul hd1 hεb (abs_nonneg _) (by positivity)
    nlinarith
  have hsq : ∀ x : ℝ, 0 ≤ x → x ≤ m → |(x - x ^ 2 / 4) ^ 2 - x ^ 2| ≤ m ^ 3 := by
    intro x hx hxm
    have h3 : x ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ hx hxm 3
    have e : (x - x ^ 2 / 4) ^ 2 - x ^ 2 = x ^ 3 * (x / 16 - 1 / 2) := by ring
    have hb : |x / 16 - 1 / 2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    rw [e, abs_mul, abs_of_nonneg (pow_nonneg hx 3)]
    calc x ^ 3 * |x / 16 - 1 / 2| ≤ x ^ 3 * 1 := mul_le_mul_of_nonneg_left hb (pow_nonneg hx 3)
      _ ≤ m ^ 3 := by linarith
  have e2 := hsq a0 h0 ha0m
  have e3 := hsq a1 h1 ha1m
  have e4 : |(a0 - a0 ^ 2 / 4) * (a1 - a1 ^ 2 / 4) - a0 * a1| ≤ m ^ 3 := by
    have e : (a0 - a0 ^ 2 / 4) * (a1 - a1 ^ 2 / 4) - a0 * a1 =
        (a0 * a1) * (-m / 4 + a0 * a1 / 16) := by rw [hmdef]; ring
    rw [e, abs_mul, abs_of_nonneg hp0]
    have := mul_le_mul (hprod.trans (by nlinarith : m ^ 2 / 4 ≤ m ^ 2)) hq (abs_nonneg _)
      (sq_nonneg m)
    exact this.trans (le_of_eq (by ring))
  have e5 : |d ^ 2 * (σ ^ 2 - 1)| ≤ m ^ 3 := by
    rw [abs_mul, hσsq, abs_of_nonneg (sq_nonneg d)]
    have := mul_le_mul ((hd.trans hprod).trans (by nlinarith : m ^ 2 / 4 ≤ m ^ 2)) hq
      (abs_nonneg _) (sq_nonneg m)
    exact this.trans (le_of_eq (by ring))
  have hXσ : ∀ x : ℝ, 0 ≤ x → x ≤ m → |(1 - x / 4) * σ - 1| ≤ m := by
    intro x hx hxm
    have hlo : (1 - m / 4) * (1 - m / 4) ≤ (1 - x / 4) * σ :=
      mul_le_mul (by linarith) hσ2 (by linarith) (by linarith)
    have hhi : (1 - x / 4) * σ ≤ 1 * 1 :=
      mul_le_mul (by linarith) hσ1 hσ0 (by norm_num)
    rw [abs_le]; constructor <;> linarith [sq_nonneg m]
  have hdXσ : ∀ x : ℝ, 0 ≤ x → x ≤ m → |d * ((x - x ^ 2 / 4) * σ - x)| ≤ m ^ 3 := by
    intro x hx hxm
    have e : d * ((x - x ^ 2 / 4) * σ - x) = d * (x * ((1 - x / 4) * σ - 1)) := by ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg hx]
    have h1' := hXσ x hx hxm
    have h2 : x * |(1 - x / 4) * σ - 1| ≤ m * m := mul_le_mul hxm h1' (abs_nonneg _) hm0
    have := mul_le_mul hd1 h2 (mul_nonneg hx (abs_nonneg _)) (by positivity)
    have h3 : m / 2 * (m * m) = m ^ 3 / 2 := by ring
    linarith
  have e6 := hdXσ a0 h0 ha0m
  have e7 := hdXσ a1 h1 ha1m
  have hid : qeJetExpr co a0 a1 d σ - qePolyExpr co a0 a1 d =
      co 1 * (d * ε) + co 2 * ((a0 - a0 ^ 2 / 4) ^ 2 - a0 ^ 2) +
        co 3 * ((a1 - a1 ^ 2 / 4) ^ 2 - a1 ^ 2) +
        co 4 * ((a0 - a0 ^ 2 / 4) * (a1 - a1 ^ 2 / 4) - a0 * a1) +
        co 5 * (d ^ 2 * (σ ^ 2 - 1)) +
        co 6 * (d * ((a0 - a0 ^ 2 / 4) * σ - a0)) +
        co 7 * (d * ((a1 - a1 ^ 2 / 4) * σ - a1)) := by
    simp only [qeJetExpr, qePolyExpr, hε]
    ring
  rw [hid, Fin.sum_univ_eight]
  have key : ∀ x y z w u v t : ℝ,
      |x + y + z + w + u + v + t| ≤ |x| + |y| + |z| + |w| + |u| + |v| + |t| := by
    intro x y z w u v t
    linarith [abs_add_le (x + y + z + w + u + v) t, abs_add_le (x + y + z + w + u) v,
      abs_add_le (x + y + z + w) u, abs_add_le (x + y + z) w, abs_add_le (x + y) z,
      abs_add_le x y]
  refine (key _ _ _ _ _ _ _).trans ?_
  have b1 := mul_le_mul_of_nonneg_left e1 (abs_nonneg (co 1))
  have b2 := mul_le_mul_of_nonneg_left e2 (abs_nonneg (co 2))
  have b3 := mul_le_mul_of_nonneg_left e3 (abs_nonneg (co 3))
  have b4 := mul_le_mul_of_nonneg_left e4 (abs_nonneg (co 4))
  have b5 := mul_le_mul_of_nonneg_left e5 (abs_nonneg (co 5))
  have b6 := mul_le_mul_of_nonneg_left e6 (abs_nonneg (co 6))
  have b7 := mul_le_mul_of_nonneg_left e7 (abs_nonneg (co 7))
  have n0 : 0 ≤ |co 0| * m ^ 3 := mul_nonneg (abs_nonneg _) hm3
  simp only [abs_mul] at b1 b5 b6 b7 ⊢
  linarith

end KAM.Planetary

end
