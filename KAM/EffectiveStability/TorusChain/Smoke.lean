/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain
public import KAM.EffectiveStability.TorusStep.Smoke

/-!
# Two-step smoke test for `torusChain_confinement` (track B, B4-TMULTI)

Two zero generators on the integrable Hamiltonian `n = 1`, `H = J₀²/2`, `Nact = H`, `P = 0`: every
premise (`TChChainOK`, `TChDomOK`, the drift inequality) is checked by kernel evaluation or
`norm_num`, and the conclusion is the zero-drift statement.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- A zero-generator smoke step on the strip `σ = 1/10`, polydisc `ρ = 5`. -/
def tchSmokeStep : TChStep := ⟨[], torusSmokeH, 1, 1 / 10, 5, 1 / 20, 1, 0, 3⟩

theorem tchSmokeStep_ok : TChStepOK 1 tchSmokeStep :=
  ⟨by norm_num [tchSmokeStep], by norm_num [tchSmokeStep], by norm_num [tchSmokeStep],
    le_rfl, by norm_num [tchSmokeStep], le_rfl, ftFits_nil 1,
    ftFits_of_check (by decide +kernel), by norm_num [tchSmokeStep, ftPiUB],
    by norm_num [tchSmokeStep, ftPiUB],
    fun i => by simp [tchSmokeStep, ftDJ, ftSupBound],
    fun i => by simp [tchSmokeStep, ftDφ, ftSupBound]⟩

/-- Two zero generators on `J₀²/2`: zero action drift on `|t| ≤ 1`. -/
theorem tchChainSmoke_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, |w₀.2 j| ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |(tchChainInv [tchSmokeStep, tchSmokeStep] (z t)).2 j - w₀.2 j| ≤ 0 := by
  have hbl : ∀ i : Fin 1, (([1] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (1 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hB : tchChainBound 1 [tchSmokeStep, tchSmokeStep] torusSmokeH = 0 := by
    decide +kernel
  have hA : ftAngleDriftBound ([] : FTPoly) 0 ftPiUB [1] = 0 := by decide +kernel
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := torusChain_confinement (n := 1)
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
    (fun _ => by norm_num) w₀ hw₀
  refine ⟨z, fun t ht j => ?_⟩
  have := (hb t ht).2 j
  simpa using this.1

end KAM.EffectiveStability
