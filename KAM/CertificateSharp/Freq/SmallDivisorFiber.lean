/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.SmallDivisorSum
public import KAM.Strip.CohomologicalSumFiber
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The fibered small-divisor bound: data and checker for clock frequencies

For `ω = (ω', 1)` (`Fin.snoc ω' 1`) the theorem `KAM.smallDivisorSum_snoc_le_fiber` needs, per
mode `k'` of `ω'` (not per mode of `ω`), the nearest integer `p_{k'}` to `-k'·ω'` and two lower
bounds. This checker produces them from the frequency box `(c, r)` of `ω'`:

* `p_{k'} = ⌊-k'·c + 1/2⌋`, checked `|k'·c + p| + ∑|k_i| r_i ≤ 1/2`;
* `L_{k'} = |k'·c + p| - ∑|k_i| r_i > 0`;
* `L₀_{k'} = |p| - 1/2` (valid and positive when `p ≠ 0`);
* `E_j = E₁^j`, `fiberConst ≤ 4 + 3.15²/3`, `π²/3 ≤ 3.15²/3`, the tail of `SdsData`.

Entries: `#{0 < |k'|₁ ≤ N}`, i.e. `2N` for `n = 2` (about `2.3·10³` at the lunar `δ₀`, against
`2.7·10⁶` for the box of `SmallDivisorSum`). `sdsFiberBound_sound` is the real statement.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate

variable {m : ℕ}

/-- The nearest integer to `-k'·c`. -/
def fiberP (box : FreqBox) (k : Fin m → ℤ) : ℤ := ⌊-(boxDot box k) + 1 / 2⌋

/-- The lower bound `L_{k'}` of `|k'·ω' + p|`. -/
def fiberLb (box : FreqBox) (k : Fin m → ℤ) : ℚ := |boxDot box k + fiberP box k| - boxRad box k

/-- The rational bound of `4 + π²/3`. -/
def fiberC0Q : ℚ := 4 + 99225 / 30000

namespace SdsData

variable (d : SdsData)

/-- The per-fiber sum. -/
def fiberSum : ℚ := ∑ k ∈ modeBox m d.N,
  (d.E1 ^ (modeNat k + (fiberP d.box k).natAbs) * ((fiberLb d.box k) ^ 2)⁻¹ +
    d.E1 ^ modeNat k * ((if fiberP d.box k = 0 then 0
      else (((fiberP d.box k).natAbs : ℚ) - 1 / 2) ^ 2)⁻¹ + d.E1 * fiberC0Q))

/-- The fibered bound of `S((ω', 1), δ)`. -/
def fiberBound : ℚ := d.E1 * (99225 / 30000) + d.fiberSum (m := m) + d.tailBound

/-- The side conditions of the fibered bound. -/
def fiberCheck : Bool :=
  decide (0 < d.γ) && decide (0 < d.δ) && decide (0 < d.cLo) && decide (1 ≤ d.E1 * d.expLow) &&
    decide (∀ k ∈ modeBox m d.N,
      0 < fiberLb d.box k ∧ |boxDot d.box k + fiberP d.box k| + boxRad d.box k ≤ 1 / 2)

end SdsData

/-- **Soundness of the fibered bound.** -/
theorem sdsFiberBound_sound (d : SdsData) (h : d.fiberCheck (m := m) = true) {ω' : Fin m → ℝ}
    (hω : FreqEncloses m d.box ω')
    (hdio : IsDiophantine (d.γ : ℝ) 1 (Fin.snoc ω' 1 : Fin (m + 1) → ℝ)) :
    smallDivisorSum (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) (d.δ : ℝ) ≤
      (d.fiberBound (m := m) : ℝ) := by
  simp only [SdsData.fiberCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hγ, hδ⟩, hc⟩, hE1⟩, hL⟩ := h
  obtain ⟨hN, hE, htail⟩ := sds_tail_le d hγ hδ hc hE1
  have hγ' : (0 : ℝ) < d.γ := by exact_mod_cast hγ
  have hδ' : (0 : ℝ) < d.δ := by exact_mod_cast hδ
  have hE0 : (0 : ℝ) ≤ (d.E1 : ℝ) := (Real.exp_pos _).le.trans hE
  have hpi := Real.pi_lt_d2
  have hpow : ∀ j : ℕ, Real.exp (-(2 * Real.pi * d.δ) * j) ≤ (d.E1 : ℝ) ^ j := fun j => by
    calc Real.exp (-(2 * Real.pi * d.δ) * j) = Real.exp (-(2 * Real.pi * d.δ)) ^ j := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hE j
  have hdist : ∀ k : Fin m → ℤ, k ∈ modeBox m d.N →
      |Diophantine.frequencyDot ω' k + fiberP d.box k| ≤ 1 / 2 ∧
      (fiberLb d.box k : ℝ) ≤ |Diophantine.frequencyDot ω' k + fiberP d.box k| := by
    intro k hk
    obtain ⟨hpos, hhalf⟩ := hL k hk
    have h1 := dot_sub_boxDot_le hω k
    have e : Diophantine.frequencyDot ω' k + fiberP d.box k -
        ((boxDot d.box k + fiberP d.box k : ℚ) : ℝ) =
        Diophantine.frequencyDot ω' k - (boxDot d.box k : ℝ) := by push_cast; ring
    have h2 : |Diophantine.frequencyDot ω' k + fiberP d.box k -
        ((boxDot d.box k + fiberP d.box k : ℚ) : ℝ)| ≤ (boxRad d.box k : ℝ) := by
      rw [e]; exact h1
    have hh := (Rat.cast_le (K := ℝ)).mpr hhalf
    have h3 := abs_sub_abs_le_abs_sub ((boxDot d.box k + fiberP d.box k : ℚ) : ℝ)
      (Diophantine.frequencyDot ω' k + fiberP d.box k)
    rw [abs_sub_comm] at h3
    have h4 := abs_sub_abs_le_abs_sub (Diophantine.frequencyDot ω' k + fiberP d.box k)
      ((boxDot d.box k + fiberP d.box k : ℚ) : ℝ)
    push_cast at h2 h3 h4 hh
    refine ⟨by linarith, ?_⟩
    unfold fiberLb
    push_cast
    linarith
  have key := smallDivisorSum_snoc_le_fiber hdio hγ' (by norm_num : (0 : ℝ) ≤ 1) hδ' hN
    (fun k => fiberP d.box k) (fun k => (fiberLb d.box k : ℝ))
    (fun k => (((fiberP d.box k).natAbs : ℝ) - 1 / 2))
    (fun k hk => (hdist k hk).1)
    (fun k hk => ⟨by exact_mod_cast (hL k hk).1, (hdist k hk).2⟩)
    (fun k hk hp => by
      have hp1 : (1 : ℝ) ≤ ((fiberP d.box k).natAbs : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp)
      refine ⟨by linarith, ?_⟩
      have h5 := (hdist k hk).1
      have h6 := abs_sub_abs_le_abs_sub ((fiberP d.box k : ℤ) : ℝ)
        (-(Diophantine.frequencyDot ω' k))
      have e : ((fiberP d.box k : ℤ) : ℝ) - -Diophantine.frequencyDot ω' k =
          Diophantine.frequencyDot ω' k + fiberP d.box k := by ring
      rw [e, abs_neg] at h6
      have e2 : ((fiberP d.box k).natAbs : ℝ) = |((fiberP d.box k : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [e2]
      linarith)
    (fun j => (d.E1 : ℝ) ^ j) hpow
  refine key.trans ?_
  unfold SdsData.fiberBound SdsData.fiberSum
  push_cast
  have hpi2 : Real.pi ^ 2 / 3 ≤ 99225 / 30000 := by
    have := Real.pi_pos
    nlinarith
  have hC : fiberConst ≤ ((fiberC0Q : ℚ) : ℝ) := by
    unfold fiberConst fiberC0Q
    push_cast
    linarith
  have hE1' : (d.E1 : ℝ) ^ 1 * (Real.pi ^ 2 / 3) ≤ (d.E1 : ℝ) * (99225 / 30000) := by
    rw [pow_one]; exact mul_le_mul_of_nonneg_left hpi2 hE0
  refine add_le_add (add_le_add hE1' (Finset.sum_le_sum fun k _ => ?_)) htail
  refine add_le_add (le_of_eq ?_) (mul_le_mul_of_nonneg_left (add_le_add (le_of_eq ?_) ?_)
    (pow_nonneg hE0 _))
  · rfl
  · split_ifs <;> simp
  · rw [pow_one]
    exact mul_le_mul_of_nonneg_left hC hE0

end KAM.CertificateSharp
