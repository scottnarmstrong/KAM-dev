/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Constants
public import KAM.Wave.Iteration.K0
public import KAM.Wave.Measure.UnpertBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the `k = 0` clause of the applicability lemma (blueprint `bpW:w6:applicable`)

Blueprint label `bpW:w6:applicable` (milestone W6), the `k = 0` clause.

`w6applicable_k0_of_shift` is a **hypothesis-taking variant** (the shift bound
`J |Ω̂_{P,J}| ≤ 3ε` is a conclusion of `bpW:w6:prep-step` (ii), which needs W5's step): for `ξ` with
`|ξ|_∞ ≤ 1/2`, `0 < α ≤ α₀`, `0 ≤ ε ≤ γα` and `Ω_0 = Ω⁰ + Ω̂_P` with `J |Ω̂_{P,J}| ≤ 3ε`:
`|⟨l, Ω_0⟩| ≥ 2β_* ⟨l⟩` for `l ∈ Λ` (W7's `three_betaStar_japL_le` gives `|⟨l, Ω⁰⟩| ≥ 3β_*⟨l⟩`, and
`|⟨l, Ω̂_P⟩| ≤ 2 · 3ε/3 ≤ 2γα ≤ β_*`). The other clauses are `w6applicable_arith`
(`Iteration/Constants`) and `w6WaveSeq_small` (`Iteration/WaveData`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- **`k = 0` clause of `bpW:w6:applicable`, hypothesis-taking variant.** -/
theorem w6applicable_k0_of_shift {m : ℝ} {hm : 0 < m} {α ε : ℝ} (hα : 0 < α)
    (hα0 : α ≤ measAlpha0 m hm) (hε : 0 ≤ ε) (hεγ : ε ≤ w6Gamma m hm * α)
    {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) {Ωh Ω0 : ℕ → ℝ}
    (hΩ0 : ∀ j, Ω0 j = omegaNor m hm ξ j + Ωh j) (hΩh : ∀ j, normLab j * |Ωh j| ≤ 3 * ε)
    {l : ℕ →₀ ℤ} (hl : IsLam l) :
    2 * measBetaStar m * japL l ≤ |linF l Ω0| := by
  have h3 := three_betaStar_japL_le m hm hξ hl
  have hj : ∀ j, |Ωh j| ≤ ε := by
    intro j
    have h := hΩh j
    have hJ := normLab_ge j
    have : 3 * |Ωh j| ≤ normLab j * |Ωh j| := mul_le_mul_of_nonneg_right hJ (abs_nonneg _)
    linarith
  have hlin := abs_linF_le_l1Norm_mul l Ωh hj
  have hl2 : (l1Norm l : ℝ) ≤ 2 := by exact_mod_cast hl.2
  have hsh : |linF l Ωh| ≤ 2 * ε := by nlinarith
  have hβ := (w6applicable_arith (m := m) (hm := hm) hα hα0).2.2.1
  have hJ := japL_ge_one l
  have hβ0 := measBetaStar_pos hm
  have e : linF l Ω0 = linF l (omegaNor m hm ξ) + linF l Ωh := by
    have : Ω0 = fun j => omegaNor m hm ξ j - (-Ωh j) := funext fun j => by rw [hΩ0]; ring
    rw [this, linF_sub']
    have : linF l (fun j => -Ωh j) = -linF l Ωh := by
      unfold linF Finsupp.sum; rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  rw [e]
  have htri := abs_sub_abs_le_abs_sub (linF l (omegaNor m hm ξ)) (-linF l Ωh)
  rw [sub_neg_eq_add, abs_neg] at htri
  have : measBetaStar m ≤ measBetaStar m * japL l := le_mul_of_one_le_right hβ0.le hJ
  nlinarith

end KAM.Wave
