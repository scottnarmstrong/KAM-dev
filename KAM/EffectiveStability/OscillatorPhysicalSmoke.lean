/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorPhysical

/-!
# Smoke test for `oscillatorStep_physical` (track B, B2-ORIG)

The harmonic oscillator `n = 1`, `χ = 0` (so `ε = 0`, `d = 0`), `H = I₀`, `Nact = q₀`, `P = 0`,
`L = 1`: the physical action is exactly conserved on `|t| ≤ 1`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

private theorem physSmoke_supBound_zero (P : CartPoly) (h : P = []) (r s : List ℚ) :
    cartSupBound P r s = 0 := by
  subst h; rfl

/-- Harmonic oscillator, `χ = 0`, physical box `a' = 0`: zero physical action drift. -/
theorem physicalSmoke_zeroDrift (z₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), z 0 = z₀ ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
        KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 0 := by
  have hρl : ∀ i : Fin 1, (([5] : List ℚ).getD i 0 : ℚ) = (5 : ℝ) := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hrl : ∀ i : Fin 1, (([2] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (2 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hB : cartSupBound (cartAdPow ([] : CartPoly) 1 (cartAction 0)) [5] [5] = 0 :=
    physSmoke_supBound_zero _ rfl _ _
  have hBr : cartSupBound (cartBracket (cartAction 0) ([] : CartPoly)) [2] [2] = 0 :=
    physSmoke_supBound_zero _ rfl _ _
  obtain ⟨T₁, -, z, h0, -, -, hb⟩ := oscillatorStep_physical
    (H := cartAction 0) (χ := []) (Nact := cartQVar 0) (P := []) (n := 1)
    (cartFits_action Nat.zero_lt_one) (cartFits_nil 1) (cartFits_qVar Nat.zero_lt_one)
    (cartFits_nil 1) (by decide +kernel) (L := 1) le_rfl (by decide +kernel)
    (ρ := 5) (δ := 1) (δc := 1) (ε := 0) one_pos one_pos le_rfl (by norm_num) [5] hρl
    (fun i => by simp [cartDq, cartSupBound]) (fun i => by simp [cartDp, cartSupBound])
    (fun _ => 0) (fun _ => 1) (fun _ => 0) 1 1 one_pos zero_le_one [2] (fun _ => 2) hrl
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => le_rfl)
    (fun j => by
      obtain rfl := Subsingleton.elim j 0
      simp only [Fin.val_zero, hBr, hB]; norm_num)
    (fun _ => by norm_num) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    z₀ hz₀
  exact ⟨z, h0, fun t ht j => by simpa using (hb t ht j).1⟩

end KAM.EffectiveStability

end
