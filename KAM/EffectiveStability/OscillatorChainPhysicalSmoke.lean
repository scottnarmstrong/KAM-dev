/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChainPhysical

/-!
# Smoke test for `oscillatorChain_physical` (track B, B2-ORIGCHAIN)

Two zero generators on the harmonic oscillator (`n = 1`, `H = I₀`, `Nact = q₀`, `P = 0`, all
tails `0`): the physical action is exactly conserved on `|t| ≤ 1`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

private theorem chainPhysSmoke_supBound_nil (P : CartPoly) (h : P = []) (r s : List ℚ) :
    cartSupBound P r s = 0 := by
  subst h; rfl

/-- Two zero generators, physical box `a' = 0`: zero physical action drift. -/
theorem chainPhysicalSmoke_zeroDrift (z₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), z 0 = z₀ ∧ ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
        KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 0 := by
  have hB : cartSupBound (cartAdPow ([] : CartPoly) 1 (cartAction 0))
      (List.replicate 1 (5 : ℚ)) (List.replicate 1 (5 : ℚ)) = 0 :=
    chainPhysSmoke_supBound_nil _ rfl _ _
  have hBr : cartSupBound (cartBracket (cartAction 0) ([] : CartPoly)) [2] [2] = 0 :=
    chainPhysSmoke_supBound_nil _ rfl _ _
  have hrl : ∀ i : Fin 1, (([2] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (2 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hstep : OscStepOK 1 (⟨[], cartAction 0, 1, 5, 1, 0⟩ : OscStep) :=
    ⟨by norm_num, le_rfl, by norm_num, le_rfl, cartFits_nil 1, cartFits_action Nat.zero_lt_one,
      fun i => by simp [cartDq, cartSupBound], fun i => by simp [cartDp, cartSupBound]⟩
  obtain ⟨T₁, -, z, h0, -, -, hb⟩ := oscillatorChain_physical
    (H := cartAction 0) (Nact := cartQVar 0) (P := []) (n := 1)
    (cartFits_action Nat.zero_lt_one) (cartFits_qVar Nat.zero_lt_one) (cartFits_nil 1)
    (by decide +kernel)
    (l := [(⟨[], cartAction 0, 1, 5, 1, 0⟩ : OscStep), ⟨[], cartAction 0, 1, 5, 1, 0⟩])
    ⟨hstep, Or.inr (by decide +kernel), hstep, Or.inr (by decide +kernel),
      (show cartEqCheck (cartAction 0) (cartAdd (cartActSubst (cartQVar 0)) []) = true by
        decide +kernel)⟩
    (δc := 1) one_pos (fun _ => 0) (fun _ => 1) (fun _ => 0) 1 1 one_pos zero_le_one [2]
    (fun _ => 2) hrl (fun _ => by norm_num) (fun _ => by norm_num)
    ⟨fun _ => by norm_num [oscTail], fun _ => by norm_num [oscTail],
      fun _ => by norm_num [oscTail], fun _ => by norm_num [oscTail], trivial⟩
    (fun _ => by norm_num)
    (fun j => by
      obtain rfl := Subsingleton.elim j 0
      simp only [Fin.val_zero, hBr, oscChainBound, hB]; norm_num)
    (fun _ => by norm_num)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => by norm_num)
    ⟨fun _ => by norm_num, fun _ => by norm_num, trivial⟩ (fun _ => by norm_num [oscTail])
    (fun _ => by norm_num [oscTail]) z₀ hz₀
  exact ⟨z, h0, fun t ht j => by simpa using (hb t ht j).1⟩

end KAM.EffectiveStability

end
