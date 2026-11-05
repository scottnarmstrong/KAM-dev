/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Fourier.Derivative
public import KAM.Frozen.Defs.IsDiophantine

/-!
# The Diophantine condition (5) through the frozen `KAM.IsDiophantine`

Source: `LP:MAIN §1 (5) (60–65)`;
track LP, non-frozen.

`isDiophantine_iff_forall_modeSize`: the frozen `KAM.IsDiophantine γ τ ω`
(`γ / (∑ i, |k_i|) ^ τ ≤ |k · ω|` for every `k ≠ 0`, D20) is literally equivalent to the form
`γ * modeSize k ^ (-τ) ≤ |k · ω|` used by the LP implementation theorems: both use the same
ℓ¹ mode size, and `s ^ (-τ) = (s ^ τ)⁻¹` for `s ≥ 0` (`Real.rpow_neg`). The equivalence holds
for every `γ`, `τ`, `ω`, with no extra premise.
-/

@[expose] public section

namespace KAM.Planetary.StrongAMD

/-- The frozen Diophantine predicate equals the `modeSize ^ (-τ)` form, pointwise in `k`
(`LP:MAIN §1 (5) (60–65)`). -/
theorem isDiophantine_iff_forall_modeSize {n : ℕ} (γ τ : ℝ) (ω : Fin n → ℝ) :
    KAM.IsDiophantine γ τ ω ↔
      ∀ k : Fin n → ℤ, k ≠ 0 →
        γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤ |∑ i, (k i : ℝ) * ω i| := by
  unfold KAM.IsDiophantine KAM.Fourier.modeSize
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [Real.rpow_neg (Finset.sum_nonneg fun i _ => abs_nonneg _), div_eq_mul_inv]

end KAM.Planetary.StrongAMD

end
