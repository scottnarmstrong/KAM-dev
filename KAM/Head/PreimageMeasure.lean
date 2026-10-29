/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.InverseFrequency
import KAM.Measure.Lipschitz

/-!
# Actions with non-Diophantine frequency

Blueprint Part 4, `bp:p4:preimage-measure`.

* `KAM.Head.preimage_measure`: if `C₃` is a constant of Theorem G3 for the bounded set
  `Ω = ∇h(B)` (the premise `hC3`, which is the conclusion of G3 at the constant `C₃`),
  then for every `α > 0` the set of actions `I ∈ B` whose frequency
  `∇h(I)` is not `(α, τ)`-Diophantine has measure at most `L₊ⁿ C₃⁺ α`, where `C₃⁺ = max (C₃, 0)`.

The proof is step `step:p4:pm-proof`: the set is contained in the image of
`{ω ∈ ∇h(B) | ω ∉ Dio_{α,τ}}` under the inverse frequency map `KAM.Head.invFreq h B`, which is
`L₊`-Lipschitz on `∇h(B)` (`KAM.Head.inverse_freq`); the image bound `KAM.lip_image` with `d = n`
and the premise `hC3` finish.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}

/-- Blueprint `bp:p4:preimage-measure`: `C3` is a constant of the frozen G3 for `Ω = ∇h(B)`. -/
theorem preimage_measure (hD : Data τ s₀ r₀ B h Lh) {C3 : ℝ}
    (hC3 : ∀ α : ℝ, 0 < α →
      volume {ω ∈ frequencyMap h '' B | ¬ IsDiophantine α τ ω} ≤ ENNReal.ofReal (C3 * α)) :
    ∀ α : ℝ, 0 < α → volume {I ∈ B | ¬ IsDiophantine α τ (frequencyMap h I)} ≤
      ENNReal.ofReal (Lplus Lh ^ n * max C3 0 * α) := by
  intro α hα
  obtain ⟨-, -, -, hlip, hleft⟩ := inverse_freq hD
  -- the set of bad actions lies in the image of the set of bad frequencies under `I_ω`
  have hsub : {I ∈ B | ¬ IsDiophantine α τ (frequencyMap h I)} ⊆
      invFreq h B '' {ω ∈ frequencyMap h '' B | ¬ IsDiophantine α τ ω} := by
    rintro I ⟨hI, hdio⟩
    exact ⟨frequencyMap h I, ⟨⟨I, hI, rfl⟩, hdio⟩, hleft I hI⟩
  -- `I_ω` is `L₊`-Lipschitz on `∇h(B)`, so the image bound applies
  have himg : volume (invFreq h B '' {ω ∈ frequencyMap h '' B | ¬ IsDiophantine α τ ω}) ≤
      ENNReal.ofReal (Lplus Lh ^ n) *
        volume {ω ∈ frequencyMap h '' B | ¬ IsDiophantine α τ ω} :=
    lip_image fun x hx y hy => hlip x hx.1 y hy.1
  have hL : 0 ≤ Lplus Lh ^ n := pow_nonneg (zero_le_one.trans (one_le_Lplus Lh)) n
  have hC : C3 * α ≤ max C3 0 * α := mul_le_mul_of_nonneg_right (le_max_left C3 0) hα.le
  calc volume {I ∈ B | ¬ IsDiophantine α τ (frequencyMap h I)}
      ≤ volume (invFreq h B '' {ω ∈ frequencyMap h '' B | ¬ IsDiophantine α τ ω}) :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (Lplus Lh ^ n) * ENNReal.ofReal (C3 * α) :=
        himg.trans (mul_le_mul' le_rfl (hC3 α hα))
    _ = ENNReal.ofReal (Lplus Lh ^ n * (C3 * α)) := (ENNReal.ofReal_mul hL).symm
    _ ≤ ENNReal.ofReal (Lplus Lh ^ n * max C3 0 * α) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hC hL

end KAM.Head

end
