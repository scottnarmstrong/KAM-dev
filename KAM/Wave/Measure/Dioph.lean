/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Wave.Measure.Lambda

/-!
# W7: from the `l = 0` condition to `KAM.IsDiophantine` (blueprint `bpW:w7:dioph`)

If `|⟨k, ω⟩| ≥ c / A_k` for all `k ≠ 0` (`A_k = 1 + |k|^{24}`), then `ν = ω / (2π)` satisfies
`KAM.IsDiophantine (c / (4π)) 24 ν`, with the frozen `IsDiophantine` (no `2π`, real exponent).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- **From the `l = 0` condition to `KAM.IsDiophantine`** (blueprint `bpW:w7:dioph`). -/
theorem isDiophantine_of_lower_bound {c : ℝ} (hc : 0 < c) {ω : Fin 2 → ℝ}
    (h : ∀ k : Fin 2 → ℤ, k ≠ 0 → c / kAk k ≤ |∑ i, (k i : ℝ) * ω i|) :
    KAM.IsDiophantine (c / (4 * π)) 24 (fun i => ω i / (2 * π)) := by
  intro k hk
  have hS := one_le_kAbs hk
  have hpi := Real.pi_pos
  have hpow : (∑ i, |(k i : ℝ)|) ^ (24 : ℝ) = kAbs k ^ 24 := by
    have : (∑ i, |(k i : ℝ)|) = kAbs k := rfl
    rw [this, show (24 : ℝ) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  have h1 : 1 ≤ kAbs k ^ 24 := one_le_pow₀ hS
  have hA := kAk_le hk
  have hApos : 0 < kAk k := by have := kAk_pos k; linarith
  have h2 : c / (2 * kAbs k ^ 24) ≤ c / kAk k :=
    div_le_div_of_nonneg_left hc.le hApos hA
  have h3 := h k hk
  have e : ∑ i, (k i : ℝ) * (ω i / (2 * π)) = (∑ i, (k i : ℝ) * ω i) / (2 * π) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < 2 * π), le_div_iff₀ (by positivity)]
  have : c / (4 * π) / kAbs k ^ 24 * (2 * π) = c / (2 * kAbs k ^ 24) := by
    field_simp; ring
  rw [this]
  exact h2.trans h3

end KAM.Wave

end
