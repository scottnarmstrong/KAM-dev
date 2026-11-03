/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChainPhysical
public import KAM.EffectiveStability.TorusChain.Smoke

/-!
# Two-step smoke test for `torusChain_physical` (track B, B4-TORIGCHAIN)

Two zero generators on `n = 1`, `H = J₀²/2`, physical box `a' = 0`: every premise is checked by
kernel evaluation or `norm_num`, and the physical action is exactly conserved on `|t| ≤ 1`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Two zero generators on `J₀²/2`, physical box `a' = 0`: zero physical action drift. -/
theorem tchChainPhysicalSmoke_zeroDrift (z₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hz₀ : ∀ j, |z₀.2 j| ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), z 0 = z₀ ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |(z t).2 j - z₀.2 j| ≤ 0 := by
  have hbl : ∀ i : Fin 1, (([1] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (1 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hB : tchChainBound 1 [tchSmokeStep, tchSmokeStep] torusSmokeH = 0 := by
    decide +kernel
  have hA : ftAngleDriftBound ([] : FTPoly) 0 ftPiUB [1] = 0 := by decide +kernel
  obtain ⟨T₁, -, z, h0, -, -, hb⟩ := torusChain_physical (n := 1)
    (H := torusSmokeH) (Nact := torusSmokeH) (P := [])
    (ftFits_of_check (by decide +kernel)) (ftFits_nil 1) (by decide +kernel)
    (l := [tchSmokeStep, tchSmokeStep])
    ⟨tchSmokeStep_ok, by decide +kernel, tchSmokeStep_ok, by decide +kernel,
      (show ftEqCheck torusSmokeH (ftAdd torusSmokeH []) = true by decide +kernel)⟩
    (δc := 1 / 20) (by norm_num) (fun _ => 0) (fun _ => 1) (fun _ => 0) 1 1 one_pos zero_le_one
    [1] hbl (fun _ => 2) (fun _ => by norm_num)
    ⟨fun _ => by norm_num [tchSmokeStep, tchTailJ], by norm_num [tchSmokeStep, tchTailA],
      fun _ => by norm_num [tchSmokeStep, tchTailJ],
      fun _ => by norm_num [tchSmokeStep, tchTailJ], by norm_num [tchSmokeStep, tchTailA],
      fun _ => by norm_num [tchSmokeStep, tchTailJ], trivial⟩
    (fun _ => by norm_num)
    (fun j => by
      obtain rfl := Subsingleton.elim j 0
      simp only [Fin.val_zero, hA, hB]; norm_num)
    (fun _ => by norm_num) (fun _ => 0) (fun _ => by norm_num [tchSmokeStep, tchTailJ])
    ⟨fun _ => by norm_num [tchSmokeStep], fun _ => by norm_num [tchSmokeStep],
      trivial⟩ z₀ hz₀
  refine ⟨z, h0, fun t ht j => ?_⟩
  have := (hb t ht j).1
  simpa [tchTailJ, tchSmokeStep] using this

end KAM.EffectiveStability

end
