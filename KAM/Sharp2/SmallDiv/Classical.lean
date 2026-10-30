/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Unimodal
public import KAM.Sharp2.SmallDiv.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The classical tail bound `T_0(b)` (blueprint `bp:p2s2sd:abel`, second part)

`sum_rpow_exp_le`: `∑_{M ≥ 1} M^p e^{-βM} ≤ Γ(p+1) β^{-p-1} + (p/(βe))^p` (unimodality: sum at most
the integral plus the maximum). `sdTail_zero_le`: `T_0(b) ≤ A_τ γ⁻² Γ(2τ+1) (4πb)^{-2τ}
(1 + ε_τ(4πb))`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace KAM.Sharp2

theorem sum_rpow_exp_le {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) :
    ∑' M : ℕ, (M : ℝ) ^ p * Real.exp (-β * M) ≤
      Real.Gamma (p + 1) * β ^ (-(p + 1)) + (p / (β * Real.exp 1)) ^ p := by
  set f : ℝ → ℝ := fun t => t ^ p * Real.exp (-(β * t)) with hf
  set c : ℝ := p / β with hc
  have hc0 : 0 < c := by positivity
  have hfeq : ∀ t : ℝ, 0 < t → f t = Real.exp (p * Real.log t - β * t) := fun t ht => by
    simp only [hf]
    rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
    congr 1; ring
  have hf0 : ∀ t, 0 ≤ t → 0 ≤ f t := fun t ht => by simp only [hf]; positivity
  have hfz : f 0 = 0 := by simp [hf, Real.zero_rpow hp.ne']
  have hcont : ContinuousOn f (Ici 0) := by
    refine ContinuousOn.mul ?_ (by fun_prop)
    exact continuousOn_id.rpow_const fun _ _ => Or.inr hp.le
  have hlogup : ∀ s t : ℝ, 0 < s → s ≤ t → p * (Real.log t - Real.log s) ≤ p * ((t - s) / s) := by
    intro s t hs hst
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < t) hs)
    rw [Real.log_div (by linarith) hs.ne'] at h
    have : (t - s) / s = t / s - 1 := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h hp.le
  have hmono : MonotoneOn f (Icc 0 c) := by
    intro s hs t ht hst
    rcases hs.1.eq_or_lt with h0 | hspos
    · rw [← h0, hfz]; exact hf0 t ht.1
    · have htpos : 0 < t := hspos.trans_le hst
      rw [hfeq s hspos, hfeq t htpos]
      refine Real.exp_le_exp.mpr ?_
      have h := Real.log_le_sub_one_of_pos (div_pos hspos htpos)
      rw [Real.log_div hspos.ne' htpos.ne'] at h
      have h1 : (1 - s / t) ≤ Real.log t - Real.log s := by linarith
      have h2 : β * (t - s) ≤ p * (1 - s / t) := by
        have : 1 - s / t = (t - s) / t := by field_simp
        rw [this, ← mul_div_assoc, le_div_iff₀ htpos]
        have : t * β ≤ p := by
          have := ht.2
          rw [hc, le_div_iff₀ hβ] at this
          linarith
        nlinarith [sub_nonneg.mpr hst]
      nlinarith
  have hanti : AntitoneOn f (Ici c) := by
    intro s hs t ht hst
    have hspos : 0 < s := hc0.trans_le hs
    rw [hfeq s hspos, hfeq t (hspos.trans_le hst)]
    refine Real.exp_le_exp.mpr ?_
    have h := hlogup s t hspos hst
    have h2 : p * ((t - s) / s) ≤ β * (t - s) := by
      rw [← mul_div_assoc, div_le_iff₀ hspos]
      have : p ≤ s * β := by
        have := hs
        rw [Set.mem_Ici, hc, div_le_iff₀ hβ] at this
        linarith
      nlinarith [sub_nonneg.mpr hst]
    nlinarith
  -- the integral
  have hkey := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (r := β) (by linarith) hβ
  have hpp : p + 1 - 1 = p := by ring
  rw [hpp] at hkey
  have hint : IntegrableOn f (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-(β * t))) (Ioi 0) :=
      .of_integral_ne_zero (by rw [hkey]; positivity)
    exact this
  have hI : ∫ t in Ioi (0 : ℝ), f t = Real.Gamma (p + 1) * β ^ (-(p + 1)) := by
    show ∫ t in Ioi (0 : ℝ), t ^ p * Real.exp (-(β * t)) = _
    rw [hkey, Real.rpow_neg hβ.le, one_div, Real.inv_rpow hβ.le, mul_comm]
  have hfc : f c = (p / (β * Real.exp 1)) ^ p := by
    simp only [hf, hc]
    have : β * (p / β) = p := by field_simp
    have h2 : p / (β * Real.exp 1) = (p / β) / Real.exp 1 := by field_simp
    rw [this, h2, Real.div_rpow hc0.le (Real.exp_pos 1).le, Real.exp_one_rpow, Real.exp_neg,
      div_eq_mul_inv]
    simp only [hc, div_eq_mul_inv]
  have hsum := sum_range_le_integral_add hc0.le hf0 hcont hmono hanti hint
  have hterm : ∀ M : ℕ, (M : ℝ) ^ p * Real.exp (-β * M) = f M := fun M => by
    simp only [hf]; rw [neg_mul]
  simp only [hterm]
  have hsm : Summable fun M : ℕ => f M := summable_of_sum_range_le (fun M => hf0 M (Nat.cast_nonneg M)) hsum
  rw [← hI, ← hfc]
  exact hsm.tsum_le_of_sum_range_le hsum

/-- **The classical tail.** -/
theorem sdTail_zero_le {τ γ b : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hb : 0 < b) :
    sdTail τ γ b 0 ≤ shellConst τ * γ⁻¹ ^ 2 *
      (Real.Gamma (2 * τ + 1) * (4 * Real.pi * b) ^ (-(2 * τ)) *
        (1 + sdEps τ (4 * Real.pi * b))) := by
  set β : ℝ := 4 * Real.pi * b with hβ
  have hβ0 : 0 < β := by positivity
  set p : ℝ := 2 * τ with hp
  have hp0 : 0 < p := by positivity
  have hA := shellConst_pos hτ.le
  have hG : 0 < Real.Gamma (p + 1) := Real.Gamma_pos_of_pos (by linarith)
  have htsum : (∑' M : ℕ, if M ≤ 0 then (0 : ℝ) else (M : ℝ) ^ p * Real.exp (-4 * Real.pi * b * M)) =
      ∑' M : ℕ, (M : ℝ) ^ p * Real.exp (-β * M) := by
    refine tsum_congr fun M => ?_
    by_cases hM : M ≤ 0
    · have : M = 0 := by omega
      subst this
      simp [Real.zero_rpow hp0.ne']
    · simp only [hM, ite_false]
      congr 2
      rw [hβ]; ring
  have hU := sum_rpow_exp_le hp0 hβ0
  have h1 : 1 - Real.exp (-4 * Real.pi * b) ≤ β := by
    have := Real.add_one_le_exp (-(4 * Real.pi * b))
    rw [show -4 * Real.pi * b = -(4 * Real.pi * b) by ring]
    linarith
  have hnn : 0 ≤ 1 - Real.exp (-4 * Real.pi * b) := by
    have : Real.exp (-4 * Real.pi * b) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  unfold sdTail
  rw [htsum]
  have hS0 : 0 ≤ ∑' M : ℕ, (M : ℝ) ^ p * Real.exp (-β * M) :=
    tsum_nonneg fun M => by positivity
  calc (1 - Real.exp (-4 * Real.pi * b)) * shellConst τ * γ⁻¹ ^ 2 *
        ∑' M : ℕ, (M : ℝ) ^ p * Real.exp (-β * M)
      ≤ β * shellConst τ * γ⁻¹ ^ 2 *
        (Real.Gamma (p + 1) * β ^ (-(p + 1)) + (p / (β * Real.exp 1)) ^ p) := by
        gcongr
    _ = _ := by
        have e1 : β ^ (-(p + 1)) = β ^ (-p) * β⁻¹ := by
          rw [show -(p + 1) = -p + -1 by ring, Real.rpow_add hβ0, Real.rpow_neg_one]
        have e2 : (p / (β * Real.exp 1)) ^ p = (p / Real.exp 1) ^ p * β ^ (-p) := by
          rw [show p / (β * Real.exp 1) = (p / Real.exp 1) / β by field_simp,
            Real.div_rpow (by positivity) hβ0.le, Real.rpow_neg hβ0.le]
          ring
        unfold sdEps
        rw [← hp, e1, e2]
        field_simp

end KAM.Sharp2

end
