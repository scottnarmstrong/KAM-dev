/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic

/-!
# Secular form: Pochhammer coefficients

Blueprint P, Part 8 (`bpP:p8:e-poch`): the rising factorial `poch`, its recurrence, the binomial
series `(1-z)^(-s) = ∑ poch s q / q! z^q` on `|z| < 1`, and the growth `poch s q / q! = O(q^(s-1))`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

def poch (s : ℝ) (q : ℕ) : ℝ := ∏ j ∈ Finset.range q, (s+j)

theorem poch_eq_ascPochhammer (s : ℝ) (q : ℕ) : poch s q = (ascPochhammer ℝ q).eval s := by
  induction q with
  | zero => simp [poch]
  | succ q ih =>
    rw [ascPochhammer_succ_eval, ← ih, poch, Finset.prod_range_succ, poch]

theorem poch_nonneg {s : ℝ} (hs : 0 < s) (q : ℕ) : 0 ≤ poch s q :=
  Finset.prod_nonneg fun j _ => by positivity

theorem poch_pos {s : ℝ} (hs : 0 < s) (q : ℕ) : 0 < poch s q :=
  Finset.prod_pos fun j _ => by positivity

theorem choose_eq_poch_div (s : ℝ) (q : ℕ) :
    Ring.choose (s + q - 1) q = poch s q / q.factorial := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer s q
  rw [Ring.multichoose_eq] at h
  rw [Polynomial.ascPochhammer_smeval_eq_eval, ← poch_eq_ascPochhammer] at h
  rw [eq_div_iff (by positivity), mul_comm, ← nsmul_eq_mul, h]

theorem poch_binomial {s : ℝ} (z : ℝ) (hz : |z| < 1) :
    HasSum (fun q : ℕ => poch s q / q.factorial * z^q) ((1-z)^(-s)) := by
  have H := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero s).hasSum
    (y := z) (by
      rw [Metric.mem_eball, edist_dist]
      simpa [Real.dist_eq, ENNReal.ofReal_lt_one] using hz)
  simp only [zero_add] at H
  convert H using 1
  · ext q
    simp [FormalMultilinearSeries.ofScalars, choose_eq_poch_div]
  · rw [one_div, ← Real.rpow_neg]
    have : 0 ≤ 1 - z := by have := (abs_lt.1 hz).2; linarith
    exact this

theorem poch_succ (s : ℝ) (q : ℕ) : poch s (q+1) = poch s q * (s+q) := by
  rw [poch, Finset.prod_range_succ, poch]

theorem poch_div_factorial_isBigO {s : ℝ} (hs : 0 < s) :
    (fun q : ℕ => poch s q / q.factorial) =O[atTop] (fun q : ℕ => (q : ℝ)^(s-1)) := by
  have hG : Tendsto (fun n : ℕ => (Real.GammaSeq s n)⁻¹) atTop (𝓝 (Real.Gamma s)⁻¹) :=
    (Real.GammaSeq_tendsto_Gamma s).inv₀ (Real.Gamma_pos_of_pos hs).ne'
  have h1 := hG.isBigO_one ℝ
  have h2 : (fun q : ℕ => (q : ℝ)^s / (s+q)) =O[atTop] (fun q : ℕ => (q : ℝ)^(s-1)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < q := by linarith
    have hpow : (0 : ℝ) < (q : ℝ)^(s-1) := Real.rpow_pos_of_pos hqpos _
    have hs' : (q : ℝ)^s = (q : ℝ)^(s-1) * q := by
      rw [← Real.rpow_add_one hqpos.ne']; ring_nf
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul, hs']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h3 := h1.mul h2
  simp only [one_mul] at h3
  refine h3.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq' : (0 : ℝ) < s + q := by positivity
  have hfac : (0 : ℝ) < (q.factorial : ℝ) := by exact_mod_cast q.factorial_pos
  have hpq : 0 < poch s q := poch_pos hs q
  simp only [Real.GammaSeq, inv_div, Finset.prod_range_succ]
  change _ * _ = _
  have : ∏ x ∈ Finset.range q, (s + (x : ℝ)) = poch s q := rfl
  rw [this]
  have hp : (0 : ℝ) < (q : ℝ)^s := Real.rpow_pos_of_pos hqpos _
  field_simp

theorem e_poch {s : ℝ} (hs : 0 < s) :
    (∀ q : ℕ, poch s (q+1) = poch s q * (s+q)) ∧
    (∀ z : ℝ, |z| < 1 → HasSum (fun q : ℕ => poch s q / q.factorial * z^q) ((1-z)^(-s))) ∧
    (fun q : ℕ => poch s q / q.factorial) =O[atTop] (fun q : ℕ => (q : ℝ)^(s-1)) :=
  ⟨poch_succ s, fun z hz => poch_binomial z hz, poch_div_factorial_isBigO hs⟩

end SecularForm
end KAM.Planetary
