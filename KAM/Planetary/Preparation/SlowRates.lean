/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.LogBounds

/-!
# Slow averaging: exponent bookkeeping (P11A-P7c, `stepP:p11:as-b2`, `as-concl`)

With `K = a ℓ`, `ℓ = log (1/ε)`, `α₁ = (γ/4) K^{-τ}`, `α₂ = ε α₁` and `E₀ = c₀ ε^{5/2} ℓ^{2τ+1}`
the displacement and `g`-bounds of the rectangular averaging lemma are exact powers of `ε` and
`ℓ`; the (B2) inequality holds for small `ε`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

section Rates

theorem rpow_nat_mul' {x : ℝ} (hx : 0 < x) (τ : ℝ) (m : ℕ) :
    x ^ ((m : ℝ) * τ) = (x ^ τ) ^ m := by
  rw [mul_comm, Real.rpow_mul hx.le, Real.rpow_natCast]

/-- `K^τ` for `K = a ℓ`. -/
theorem rpow_mul_pos {a l : ℝ} (ha : 0 < a) (hl : 0 < l) (τ : ℝ) :
    (a * l) ^ τ = a ^ τ * l ^ τ := Real.mul_rpow ha.le hl.le

theorem eps_pow_five_half {eps : ℝ} (h : 0 < eps) :
    eps ^ (5 / 2 : ℝ) = eps ^ 2 * eps ^ (1 / 2 : ℝ) := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add h]
  norm_num

theorem eps_pow_three_half {eps : ℝ} (h : 0 < eps) :
    eps ^ (3 / 2 : ℝ) = eps * eps ^ (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one]

theorem lg_pow_one {l : ℝ} (h : 0 < l) (τ : ℝ) (m : ℕ) :
    l ^ ((m : ℝ) * τ + 1) = (l ^ τ) ^ m * l := by
  rw [Real.rpow_add h, rpow_nat_mul' h, Real.rpow_one]

theorem lg_pow_two {l : ℝ} (h : 0 < l) (τ : ℝ) (m : ℕ) :
    l ^ ((m : ℝ) * τ + 2) = (l ^ τ) ^ m * l ^ 2 := by
  rw [Real.rpow_add h, rpow_nat_mul' h]
  norm_num

variable {eps l a γ τ s c0 : ℝ}

/-- `ρ`-block and `J`-block displacement constants: `3E₀/(2π α s)` for `α = ε^j (γ/4) K^{-τ}`. -/
theorem slow_disp_rho (heps : 0 < eps) (hl : 0 < l) (ha : 0 < a) (hγ : 0 < γ) (hs : 0 < s) :
    3 * (c0 * eps ^ (5 / 2 : ℝ) * l ^ (2 * τ + 1)) /
      (2 * Real.pi * (eps * (γ / 4 * (a * l) ^ (-τ))) * s) =
      6 * c0 * a ^ τ / (Real.pi * γ * s) * (eps ^ (3 / 2 : ℝ) * l ^ (3 * τ + 1)) := by
  have h1 := lg_pow_one hl τ 2
  have h2 := lg_pow_one hl τ 3
  push_cast at h1 h2
  rw [eps_pow_five_half heps, eps_pow_three_half heps, h1, h2, Real.rpow_neg (by positivity),
    rpow_mul_pos ha hl]
  have hlt : 0 < l ^ τ := Real.rpow_pos_of_pos hl _
  have hat : 0 < a ^ τ := Real.rpow_pos_of_pos ha _
  have := Real.pi_pos
  field_simp
  ring

theorem slow_disp_J (heps : 0 < eps) (hl : 0 < l) (ha : 0 < a) (hγ : 0 < γ) (hs : 0 < s) :
    3 * (c0 * eps ^ (5 / 2 : ℝ) * l ^ (2 * τ + 1)) /
      (2 * Real.pi * (γ / 4 * (a * l) ^ (-τ)) * s) =
      6 * c0 * a ^ τ / (Real.pi * γ * s) * (eps ^ (5 / 2 : ℝ) * l ^ (3 * τ + 1)) := by
  have h1 := lg_pow_one hl τ 2
  have h2 := lg_pow_one hl τ 3
  push_cast at h1 h2
  rw [h1, h2, Real.rpow_neg (by positivity), rpow_mul_pos ha hl]
  have hlt : 0 < l ^ τ := Real.rpow_pos_of_pos hl _
  have hat : 0 < a ^ τ := Real.rpow_pos_of_pos ha _
  have := Real.pi_pos
  field_simp
  ring

theorem slow_disp_theta (heps : 0 < eps) (hl : 0 < l) (ha : 0 < a) (hγ : 0 < γ) :
    9 * (c0 * eps ^ (5 / 2 : ℝ) * l ^ (2 * τ + 1)) /
      (2 * Real.pi * (eps * (γ / 4 * (a * l) ^ (-τ))) * (Real.pi * eps)) =
      18 * c0 * a ^ τ / (Real.pi ^ 2 * γ) * (eps ^ (1 / 2 : ℝ) * l ^ (3 * τ + 1)) := by
  have h1 := lg_pow_one hl τ 2
  have h2 := lg_pow_one hl τ 3
  push_cast at h1 h2
  rw [eps_pow_five_half heps, h1, h2, Real.rpow_neg (by positivity), rpow_mul_pos ha hl]
  have hlt : 0 < l ^ τ := Real.rpow_pos_of_pos hl _
  have hat : 0 < a ^ τ := Real.rpow_pos_of_pos ha _
  have := Real.pi_pos
  field_simp
  ring

theorem slow_g_quad (heps : 0 < eps) (hl : 0 < l) (ha : 0 < a) (hγ : 0 < γ) (hs : 0 < s) :
    130 * (c0 * eps ^ (5 / 2 : ℝ) * l ^ (2 * τ + 1)) ^ 2 /
      (2 * Real.pi * (eps * (γ / 4 * (a * l) ^ (-τ))) * (Real.pi * eps) * s) =
      260 * c0 ^ 2 * a ^ τ / (Real.pi ^ 2 * γ * s) * (eps ^ 3 * l ^ (5 * τ + 2)) := by
  have h1 := lg_pow_one hl τ 2
  have h2 := lg_pow_two hl τ 5
  push_cast at h1 h2
  have h3 : (c0 * eps ^ (5 / 2 : ℝ) * l ^ (2 * τ + 1)) ^ 2 =
      c0 ^ 2 * (eps ^ 5 * ((l ^ τ) ^ 4 * l ^ 2)) := by
    have he : (eps ^ (5 / 2 : ℝ)) ^ 2 = eps ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul heps.le,
        show (5 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [mul_pow, mul_pow, h1, he]
    ring
  rw [h3, h2, Real.rpow_neg (by positivity), rpow_mul_pos ha hl]
  have hlt : 0 < l ^ τ := Real.rpow_pos_of_pos hl _
  have hat : 0 < a ^ τ := Real.rpow_pos_of_pos ha _
  have := Real.pi_pos
  field_simp
  ring

end Rates

end KAM.Planetary

end
