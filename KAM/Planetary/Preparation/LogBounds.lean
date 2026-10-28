/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Logarithmic domination (P11A-P5, `bpP:p11:e4`)

`e4` is the elementary fact `ε ^ a * (log (1/ε)) ^ b → 0` as `ε → 0+` for `a > 0`, `b ≥ 0`; its
companion `log_inv_ge_one` is the first clause `log (1/ε) ≥ 1` on `(0, e⁻¹]`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

/-- `bpP:p11:e4`, first clause: `log (1/ε) ≥ 1` for `0 < ε ≤ e⁻¹`. -/
theorem log_inv_ge_one {eps : ℝ} (h0 : 0 < eps) (h1 : eps ≤ Real.exp (-1)) :
    1 ≤ Real.log (1/eps) := by
  rw [one_div, Real.log_inv]
  have := Real.log_le_log h0 h1
  rw [Real.log_exp] at this
  linarith

/-- Generic logarithmic domination needed in both finite averaging stages and wr-nu. -/
theorem e4 {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Tendsto (fun eps : ℝ => eps^a*Real.log (1/eps)^b) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [Real.rpow_zero, mul_one]
    have := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have key : Tendsto (fun eps : ℝ => (-(Real.log eps) * eps^(a/b)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have := (tendsto_log_mul_rpow_nhdsGT_zero (div_pos ha hb')).neg
      simpa [neg_mul] using this
    have hpow := (Real.continuousAt_rpow_const 0 b (Or.inr hb)).tendsto.comp key
    rw [Real.zero_rpow hb'.ne'] at hpow
    refine hpow.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with eps he
    simp only [Function.comp, one_div, Real.log_inv]
    have hl : 0 ≤ -Real.log eps := neg_nonneg.2 (Real.log_nonpos he.1.le he.2.le)
    rw [Real.mul_rpow hl (Real.rpow_nonneg he.1.le _), ← Real.rpow_mul he.1.le,
      div_mul_cancel₀ _ hb'.ne', mul_comm]

end KAM.Planetary

end
