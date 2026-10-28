/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Parameters

/-!
# P Part 5: parameter algebra for the thresholds (`bpP:p5:param-facts`, `bpP:p5:rK`)

Pointwise inequalities for `params d r mu` on the range `r ≤ e⁻¹`, `0 < mu < r^6/(log 1/r)^c`,
`LP ≤ log 1/r`, `r^2 (log 1/r)^(τ+1) ≤ 1`: the bound `gammaBar ≤ Cγ √r`, the displacement ratio
`LP mu Kbar^τ/gammaBar ≤ √r r^5/(G κ^{1/2})`, and the numerical consequences of `PGScaleSpec`
(`ĉ Ê < 1`, `rK < ρ̂/(256 n)`). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-TH.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {a b : ℕ}

theorem pgWidth_lt_one (d : PGData a b) : pgWidth d < 1 := by
  unfold pgWidth; linarith [(pgExtension d).delta_lt]

theorem one_le_pgKappa (d : PGData a b) : 1 ≤ 30 / pgWidth d := by
  rw [le_div_iff₀ (pgWidth_pos d)]; linarith [pgWidth_lt_one d]

theorem one_le_log_inv {r : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1)) :
    1 ≤ Real.log (1/r) := by
  rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hr0]
  have := mul_le_mul_of_nonneg_left hr (Real.exp_pos 1).le
  rw [← Real.exp_add] at this
  simpa using this

theorem LP_mul_mu_le {LP mu r τ : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1)) (hmu0 : 0 < mu)
    (hLP : LP ≤ Real.log (1/r)) (hmu : mu < r^6/(Real.log (1/r))^(2*τ+2)) :
    LP*mu ≤ r^6 * (Real.log (1/r))^(-(2*τ+1)) := by
  have hL : 1 ≤ Real.log (1/r) := one_le_log_inv hr0 hr
  set L := Real.log (1/r)
  have hL0 : 0 < L := by linarith
  have hX : 0 < L^(2*τ+1) := Real.rpow_pos_of_pos hL0 _
  have h1 : mu * L^(2*τ+2) < r^6 := by
    rwa [lt_div_iff₀ (Real.rpow_pos_of_pos hL0 _)] at hmu
  have h2 : L^(2*τ+2) = L * L^(2*τ+1) := by
    rw [show 2*τ+2 = 1 + (2*τ+1) by ring, Real.rpow_add hL0, Real.rpow_one]
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ hX]
  calc LP*mu*L^(2*τ+1) ≤ L*mu*L^(2*τ+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLP hmu0.le) hX.le
    _ = mu * L^(2*τ+2) := by rw [h2]; ring
    _ ≤ r^6 := h1.le

theorem sqrt_LP_mu_le {LP mu r τ : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1))
    (h : LP*mu ≤ r^6 * (Real.log (1/r))^(-(2*τ+1))) :
    Real.sqrt (LP*mu) ≤ r^3 * (Real.log (1/r))^(-(τ+1/2)) := by
  have hL0 : 0 < Real.log (1/r) := by linarith [one_le_log_inv hr0 hr]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e : (Real.log (1/r) ^ (-(τ+1/2)))^2 = Real.log (1/r) ^ (-(2*τ+1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1; push_cast; ring
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, e, ← pow_mul]

end KAM.Planetary

end
