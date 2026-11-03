/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusStep

/-!
# Smoke test for `torusStep_confinement` (track B, B4-TSTEP)

The integrable Hamiltonian `n = 1`, `H = J₀²/2`, `χ = 0`, `Nact = H`, `P = 0`, `L = 1`: the identity
`hid` and every majorant premise are checked by kernel evaluation or `norm_num`, and the conclusion
is the zero-drift statement.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- The integrable Hamiltonian `J₀² / 2`. -/
def torusSmokeH : FTPoly := [⟨[], [2], 0, 1 / 2, 0⟩]

/-- Integrable `H = J₀²/2`, `χ = 0`, `P = 0`, `L = 1`: zero action drift on `|t| ≤ 1`. -/
theorem torusStepSmoke_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, |w₀.2 j| ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |(torusChartInv ([] : FTPoly) (1 / 10 : ℝ) (5 : ℝ) (z t)).2 j - w₀.2 j| ≤ 0 := by
  have hρl : ∀ i : Fin 1, (([5] : List ℚ).getD i 0 : ℚ) = (5 : ℝ) := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hbl : ∀ i : Fin 1, (([1] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (1 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hB : ftSupBound (ftAdPow ([] : FTPoly) 1 torusSmokeH) ftPiUB 3 [5] = 0 := by
    decide +kernel
  have hA : ftAngleDriftBound ([] : FTPoly) 0 ftPiUB [1] = 0 := by decide +kernel
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := torusStep_confinement (n := 1)
    (H := torusSmokeH) (χ := []) (Nact := torusSmokeH) (P := [])
    (ftFits_of_check (by decide +kernel)) (ftFits_nil 1) (ftFits_nil 1) (by decide +kernel)
    (L := 1) le_rfl (by decide +kernel)
    (σ := 1 / 10) (ρ := 5) (σ' := 1 / 20) (ρ' := 1) (δc := 1 / 20) (ε := 0)
    (by norm_num) one_pos (by norm_num) le_rfl (by norm_num)
    (πub := ftPiUB) (lam := 3) pi_le_ftPiUB (by norm_num [ftPiUB]) (by norm_num [ftPiUB])
    [5] hρl (fun i => by simp [ftDJ, ftSupBound]) (fun i => by simp [ftDφ, ftSupBound])
    (fun _ => 0) (fun _ => 1) (fun _ => 0) 1 1 one_pos zero_le_one [1] hbl (fun _ => 2)
    (fun _ => by norm_num) (by norm_num) (fun _ => by norm_num) (by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl)
    (fun j => by
      obtain rfl := Subsingleton.elim j 0
      simp only [Fin.val_zero, hA, hB]; norm_num)
    (fun _ => by norm_num) w₀ hw₀
  refine ⟨z, fun t ht j => ?_⟩
  have := (hb t ht).2 j
  simpa using this.1

end KAM.EffectiveStability
