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

/-- `stepP:p11:as-b2` (B2), for `K = a ℓ`: `c₀ ε^{5/2} ℓ^{2τ+1} ≤ α₂ π ε/(128 K)` for small `ε`. -/
theorem slow_b2_eventually (c0 : ℝ) (ha : 0 < a) (hγ : 0 < γ) (hτ : 0 ≤ τ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0),
      c0 * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * τ + 1) ≤
        (eps * (γ / 4 * (a * Real.log (1 / eps)) ^ (-τ))) * Real.pi * eps /
          (128 * (a * Real.log (1 / eps))) := by
  have he := e4 (a := (1 / 2 : ℝ)) (b := 3 * τ + 2) (by norm_num) (by linarith)
  have hlim := he.const_mul (|c0| * a ^ (τ + 1))
  rw [mul_zero] at hlim
  have hπ := Real.pi_pos
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < γ * Real.pi / 512 by positivity))
  have h01 : ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps ∈ Ioo (0 : ℝ) (Real.exp (-1)) :=
    Ioo_mem_nhdsGT (Real.exp_pos _)
  filter_upwards [hev, h01] with eps h1 h2
  obtain ⟨he0, he1⟩ := h2
  have hl : 0 < Real.log (1 / eps) := by
    have := log_inv_ge_one he0 he1.le
    linarith
  set l := Real.log (1 / eps) with hldef
  have hK : 0 < a * l := by positivity
  have hKτ : 0 < (a * l) ^ τ := Real.rpow_pos_of_pos hK _
  have hlhs : c0 * eps ^ (5 / 2 : ℝ) * l ^ (2 * τ + 1) =
      eps ^ 2 * (c0 * eps ^ (1 / 2 : ℝ) * l ^ (2 * τ + 1)) := by
    rw [eps_pow_five_half he0]; ring
  have hrhs : (eps * (γ / 4 * (a * l) ^ (-τ))) * Real.pi * eps / (128 * (a * l)) =
      eps ^ 2 * (γ * Real.pi / 512 / ((a * l) ^ τ * (a * l))) := by
    rw [Real.rpow_neg hK.le]
    field_simp
    ring
  rw [hlhs, hrhs]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [le_div_iff₀ (by positivity)]
  have hpow : l ^ (2 * τ + 1) * ((a * l) ^ τ * (a * l)) = a ^ (τ + 1) * l ^ (3 * τ + 2) := by
    rw [← Real.rpow_add_one hK.ne', Real.mul_rpow ha.le hl.le]
    have : l ^ (3 * τ + 2) = l ^ (2 * τ + 1) * l ^ (τ + 1) := by
      rw [← Real.rpow_add hl]; ring_nf
    rw [this]; ring
  calc c0 * eps ^ (1 / 2 : ℝ) * l ^ (2 * τ + 1) * ((a * l) ^ τ * (a * l))
      = c0 * (eps ^ (1 / 2 : ℝ) * (l ^ (2 * τ + 1) * ((a * l) ^ τ * (a * l)))) := by ring
    _ = c0 * a ^ (τ + 1) * (eps ^ (1 / 2 : ℝ) * l ^ (3 * τ + 2)) := by rw [hpow]; ring
    _ ≤ |c0| * a ^ (τ + 1) * (eps ^ (1 / 2 : ℝ) * l ^ (3 * τ + 2)) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self c0) (by positivity)) (by positivity)
    _ ≤ γ * Real.pi / 512 := h1.le

end Rates

end KAM.Planetary

end
