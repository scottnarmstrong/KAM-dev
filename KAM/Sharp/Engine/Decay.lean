/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Engine.Schedule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Decay of the errors of the sharp Newton engine (blueprint `bp:p2s:decay`)

`ε₀ = e`, `ε_{s+1} = C_E ε_s²/(γ⁴ δ_s^{2a})`. Under `2^{2a} C_E e/(γ⁴ δ₀^{2a}) ≤ 1` we get
`ε_s ≤ 2^{-2as} e` by a direct induction (no positivity of `C_E` is needed), then the weighted
bounds and the geometric sums.
-/

@[expose] public noncomputable section

namespace KAM.Sharp.Engine

/-- `ε₀ = e`, `ε_{s+1} = C_E ε_s² / (γ⁴ δ_s^{2a})`. -/
def epsSeq (CE a lam ρ ρinf γ e : ℝ) : ℕ → ℝ
  | 0 => e
  | s + 1 => CE * epsSeq CE a lam ρ ρinf γ e s ^ 2 / (γ ^ 4 * deltaSeq lam ρ ρinf s ^ (2 * a))

section Errors

variable {CE a lam ρ ρinf γ e : ℝ}

theorem epsSeq_zero : epsSeq CE a lam ρ ρinf γ e 0 = e := rfl

theorem epsSeq_nonneg (hCE : 0 ≤ CE) (hlam : 0 < lam) (hρ : ρinf < ρ) (he : 0 ≤ e) (s : ℕ) :
    0 ≤ epsSeq CE a lam ρ ρinf γ e s := by
  induction s with
  | zero => exact he
  | succ s ih =>
    have hδ := (deltaSeq_pos hlam hρ s).le
    simp only [epsSeq]
    positivity

/-- `ε_s ≤ 2^{-2as} e`. -/
theorem epsSeq_le (hCE : 0 ≤ CE) (hlam : 0 < lam) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * a) * CE * e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ 1) (s : ℕ) :
    epsSeq CE a lam ρ ρinf γ e s ≤ (2 : ℝ) ^ (-(2 * a * s)) * e := by
  have hd0 := delta0_pos hlam hρ
  have hD : 0 < γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)
  have hq' : (2 : ℝ) ^ (2 * a) * CE * e ≤ γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a) :=
    (div_le_one hD).mp hq
  have h2a : (0 : ℝ) < (2 : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ (-(2 * a)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have hq'' : CE * e ≤ (2 : ℝ) ^ (-(2 * a)) * (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) := by
    have := mul_le_mul_of_nonneg_left hq' (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(2 * a)))
    calc CE * e = (2 : ℝ) ^ (-(2 * a)) * ((2 : ℝ) ^ (2 * a) * CE * e) := by
          rw [← mul_assoc, ← mul_assoc, mul_comm ((2 : ℝ) ^ (-(2 * a))), hinv]; ring
      _ ≤ _ := this
  induction s with
  | zero => simp [epsSeq_zero]
  | succ s ih =>
    have hnn := epsSeq_nonneg hCE hlam hρ he (a := a) (γ := γ) s
    have ht : 0 < (2 : ℝ) ^ (-(2 * a * s)) := Real.rpow_pos_of_pos (by norm_num) _
    have hsplit : (2 : ℝ) ^ (-(2 * a * ((s + 1 : ℕ) : ℝ))) =
        (2 : ℝ) ^ (-(2 * a * s)) * (2 : ℝ) ^ (-(2 * a)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
    have hδ : deltaSeq lam ρ ρinf s ^ (2 * a) =
        (2 : ℝ) ^ (-(2 * a * s)) * delta0 lam ρ ρinf ^ (2 * a) :=
      deltaSeq_rpow hd0.le _ _
    simp only [epsSeq]
    rw [hδ, hsplit]
    set t := (2 : ℝ) ^ (-(2 * a * s))
    set u := (2 : ℝ) ^ (-(2 * a))
    set Dd := delta0 lam ρ ρinf ^ (2 * a)
    have hDd : 0 < Dd := Real.rpow_pos_of_pos hd0 _
    rw [div_le_iff₀ (by positivity)]
    have h1 : epsSeq CE a lam ρ ρinf γ e s ^ 2 ≤ (t * e) ^ 2 :=
      pow_le_pow_left₀ hnn ih 2
    calc CE * epsSeq CE a lam ρ ρinf γ e s ^ 2 ≤ CE * (t * e) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hCE
      _ = t * e * t * (CE * e) := by ring
      _ ≤ t * e * t * (u * (γ ^ 4 * Dd)) :=
          mul_le_mul_of_nonneg_left hq'' (by positivity)
      _ = t * u * e * (γ ^ 4 * (t * Dd)) := by ring

/-- The weighted bounds `ε_s/δ_s^i ≤ 2^{-(2a-i)s} e/δ₀^i ≤ e/δ₀^i` for `0 ≤ i ≤ 2a`. -/
theorem epsSeq_weighted (hCE : 0 ≤ CE) (hlam : 0 < lam) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * a) * CE * e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ 1) {i : ℝ}
    (_hi : 0 ≤ i) (hi2 : i ≤ 2 * a) (s : ℕ) :
    epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i ≤
        (2 : ℝ) ^ (-((2 * a - i) * s)) * e / delta0 lam ρ ρinf ^ i ∧
      (2 : ℝ) ^ (-((2 * a - i) * s)) * e / delta0 lam ρ ρinf ^ i ≤ e / delta0 lam ρ ρinf ^ i := by
  have hd0 := delta0_pos hlam hρ
  have hDj : 0 < delta0 lam ρ ρinf ^ i := Real.rpow_pos_of_pos hd0 _
  have hsplit : (2 : ℝ) ^ (-((2 * a - i) * (s : ℝ))) =
      (2 : ℝ) ^ (-(2 * a * (s : ℝ))) / (2 : ℝ) ^ (-(i * (s : ℝ))) := by
    rw [← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · have hε := epsSeq_le hCE hlam hρ hγ he hq s
    rw [deltaSeq_rpow hd0.le, hsplit]
    calc _ ≤ (2 : ℝ) ^ (-(2 * a * (s : ℝ))) * e /
          ((2 : ℝ) ^ (-(i * (s : ℝ))) * delta0 lam ρ ρinf ^ i) :=
          div_le_div_of_nonneg_right hε (by positivity)
      _ = _ := by
          have : (0 : ℝ) < (2 : ℝ) ^ (-(i * (s : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
          field_simp
  · have h1 : (2 : ℝ) ^ (-((2 * a - i) * (s : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (mul_nonneg (by linarith) (Nat.cast_nonneg s)))
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left he h1) hDj.le

/-- The sums `∑ ε_s/δ_s^i ≤ 2e/δ₀^i` for `0 ≤ i ≤ 2a - 1`. -/
theorem epsSeq_sum (hCE : 0 ≤ CE) (hlam : 0 < lam) (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * a) * CE * e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ 1) {i : ℝ}
    (hi : 0 ≤ i) (hi2 : i ≤ 2 * a - 1) :
    Summable (fun s => epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i) ∧
      ∑' s, epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i ≤
        2 * e / delta0 lam ρ ρinf ^ i := by
  have hd0 := delta0_pos hlam hρ
  have hDj : 0 < delta0 lam ρ ρinf ^ i := Real.rpow_pos_of_pos hd0 _
  set r : ℝ := (2 : ℝ) ^ (-(2 * a - i)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r ≤ 1 / 2 := by
    have : r ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  have hgeo : ∀ s : ℕ, (2 : ℝ) ^ (-((2 * a - i) * (s : ℝ))) = r ^ s := by
    intro s
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hle : ∀ s : ℕ, epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i ≤
      e / delta0 lam ρ ρinf ^ i * r ^ s := by
    intro s
    have := (epsSeq_weighted hCE hlam hρ hγ he hq hi (by linarith) s).1
    rw [hgeo] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hnn : ∀ s : ℕ, 0 ≤ epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i := by
    intro s
    have := epsSeq_nonneg hCE hlam hρ he (a := a) (γ := γ) s
    have := Real.rpow_pos_of_pos (deltaSeq_pos hlam hρ s) i
    positivity
  have hsum : Summable (fun s : ℕ => e / delta0 lam ρ ρinf ^ i * r ^ s) :=
    (summable_geometric_of_lt_one hr0.le (by linarith)).mul_left _
  refine ⟨Summable.of_nonneg_of_le hnn hle hsum, ?_⟩
  calc _ ≤ ∑' s : ℕ, e / delta0 lam ρ ρinf ^ i * r ^ s :=
        (Summable.of_nonneg_of_le hnn hle hsum).tsum_le_tsum hle hsum
    _ = e / delta0 lam ρ ρinf ^ i * (1 - r)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le (by linarith)]
    _ ≤ e / delta0 lam ρ ρinf ^ i * 2 := by
        have h2 : (1 - r)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * e / delta0 lam ρ ρinf ^ i := by ring

end Errors

/-- Blueprint `bp:p2s:decay`. -/
theorem error_decay {CE a lam ρ ρinf γ e : ℝ} (hCE : 0 ≤ CE) (ha : 2 ≤ a) (hlam : 0 < lam)
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ) (he : 0 ≤ e)
    (hq : (2 : ℝ) ^ (2 * a) * CE * e / (γ ^ 4 * delta0 lam ρ ρinf ^ (2 * a)) ≤ 1) :
    (∀ s, 0 ≤ epsSeq CE a lam ρ ρinf γ e s ∧
      epsSeq CE a lam ρ ρinf γ e s ≤ (2 : ℝ) ^ (-(2 * a * s)) * e) ∧
    (∀ (i : ℝ) (s : ℕ), 0 ≤ i → i ≤ 2 * a →
      epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i ≤ e / delta0 lam ρ ρinf ^ i) ∧
    ∀ i : ℝ, 0 ≤ i → i ≤ 2 * a - 1 →
      Summable (fun s => epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i) ∧
      ∑' s, epsSeq CE a lam ρ ρinf γ e s / deltaSeq lam ρ ρinf s ^ i ≤
        2 * e / delta0 lam ρ ρinf ^ i := by
  have _ := hρinf
  have _ := ha
  exact ⟨fun s => ⟨epsSeq_nonneg hCE hlam hρ he s, epsSeq_le hCE hlam hρ hγ he hq s⟩,
    fun i s hi hi2 => ((epsSeq_weighted hCE hlam hρ hγ he hq hi hi2 s).1.trans
      (epsSeq_weighted hCE hlam hρ hγ he hq hi hi2 s).2),
    fun i hi hi2 => epsSeq_sum hCE hlam hρ hγ he hq hi hi2⟩

end KAM.Sharp.Engine

end
