/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The schedule of the sharp Newton engine (blueprint `bp:p2s:schedule`)

`δ₀ = min {1, (ρ - ρ∞)/(2λ)}`, `δ_s = 2^{-s} δ₀`, `r_s = ρ - 2λδ₀(1 - 2^{-s})`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp.Engine

/-- `δ₀ = min {1, (ρ - ρ∞)/(2λ)}` (`bp:p2s:schedule`). -/
def delta0 (lam ρ ρinf : ℝ) : ℝ := min 1 ((ρ - ρinf) / (2 * lam))
/-- `δ_s = 2^{-s} δ₀`. -/
def deltaSeq (lam ρ ρinf : ℝ) (s : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ s * delta0 lam ρ ρinf
/-- `r_s = ρ - 2λδ₀(1 - 2^{-s})`. -/
def rSeq (lam ρ ρinf : ℝ) (s : ℕ) : ℝ := ρ - 2 * lam * delta0 lam ρ ρinf * (1 - (2 : ℝ)⁻¹ ^ s)

section Sequences

variable {lam ρ ρinf : ℝ}

theorem delta0_pos (hlam : 0 < lam) (hρ : ρinf < ρ) : 0 < delta0 lam ρ ρinf :=
  lt_min one_pos (div_pos (by linarith) (by positivity))

theorem delta0_le_one (lam ρ ρinf : ℝ) : delta0 lam ρ ρinf ≤ 1 := min_le_left _ _

theorem two_mul_lam_delta0_le (hlam : 0 < lam) :
    2 * lam * delta0 lam ρ ρinf ≤ ρ - ρinf := by
  have h : delta0 lam ρ ρinf ≤ (ρ - ρinf) / (2 * lam) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h
  linarith

theorem deltaSeq_zero : deltaSeq lam ρ ρinf 0 = delta0 lam ρ ρinf := by simp [deltaSeq]

theorem deltaSeq_pos (hlam : 0 < lam) (hρ : ρinf < ρ) (s : ℕ) : 0 < deltaSeq lam ρ ρinf s :=
  mul_pos (pow_pos (by norm_num) s) (delta0_pos hlam hρ)

theorem deltaSeq_le_delta0 (hlam : 0 < lam) (hρ : ρinf < ρ) (s : ℕ) :
    deltaSeq lam ρ ρinf s ≤ delta0 lam ρ ρinf := by
  have h1 : (2 : ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 := delta0_pos hlam hρ
  unfold deltaSeq
  nlinarith

theorem deltaSeq_succ (s : ℕ) : deltaSeq lam ρ ρinf (s + 1) = deltaSeq lam ρ ρinf s / 2 := by
  unfold deltaSeq
  rw [pow_succ]
  ring

/-- `δ_s ^ x = 2 ^ (-(x s)) δ₀ ^ x`, for real `x`. -/
theorem deltaSeq_rpow (hd0 : 0 ≤ delta0 lam ρ ρinf) (x : ℝ) (s : ℕ) :
    deltaSeq lam ρ ρinf s ^ x = (2 : ℝ) ^ (-(x * s)) * delta0 lam ρ ρinf ^ x := by
  have h2 : (2 : ℝ)⁻¹ ^ s = (2 : ℝ) ^ (-(s : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  unfold deltaSeq
  rw [Real.mul_rpow (by positivity) hd0, h2, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

theorem rSeq_zero : rSeq lam ρ ρinf 0 = ρ := by simp [rSeq]

/-- `r_s = ρ - 2λδ₀ + 2λδ_s`. -/
theorem rSeq_eq (s : ℕ) :
    rSeq lam ρ ρinf s = ρ - 2 * lam * delta0 lam ρ ρinf + 2 * lam * deltaSeq lam ρ ρinf s := by
  unfold rSeq deltaSeq
  ring

theorem rSeq_succ (s : ℕ) :
    rSeq lam ρ ρinf (s + 1) = rSeq lam ρ ρinf s - lam * deltaSeq lam ρ ρinf s := by
  rw [rSeq_eq, rSeq_eq, deltaSeq_succ]
  ring

end Sequences

/-- Blueprint `bp:p2s:schedule`. -/
theorem schedule {lam ρ ρinf : ℝ} (hlam : 0 < lam) (hρinf : 0 < ρinf) (hρ : ρinf < ρ) :
    0 < delta0 lam ρ ρinf ∧ delta0 lam ρ ρinf ≤ 1 ∧ rSeq lam ρ ρinf 0 = ρ ∧
    (∀ s, rSeq lam ρ ρinf (s + 1) = rSeq lam ρ ρinf s - lam * deltaSeq lam ρ ρinf s) ∧
    (∀ s, ρinf < rSeq lam ρ ρinf s) ∧
    (∀ s, 0 < deltaSeq lam ρ ρinf s ∧ deltaSeq lam ρ ρinf s ≤ 1) ∧
    ∀ s, lam * deltaSeq lam ρ ρinf s < rSeq lam ρ ρinf s := by
  have h8 := two_mul_lam_delta0_le (ρ := ρ) (ρinf := ρinf) hlam
  have hr : ∀ s, ρinf < rSeq lam ρ ρinf s := fun s => by
    have := mul_pos (mul_pos two_pos hlam) (deltaSeq_pos hlam hρ s)
    rw [rSeq_eq]; linarith
  refine ⟨delta0_pos hlam hρ, delta0_le_one _ _ _, rSeq_zero, rSeq_succ, hr,
    fun s => ⟨deltaSeq_pos hlam hρ s,
      (deltaSeq_le_delta0 hlam hρ s).trans (delta0_le_one _ _ _)⟩, fun s => ?_⟩
  have := hr (s + 1)
  rw [rSeq_succ] at this
  linarith

end KAM.Sharp.Engine

end
