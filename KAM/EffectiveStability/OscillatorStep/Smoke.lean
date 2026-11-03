/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorStep

/-!
# Smoke test for `oscillatorStep_confinement` (track B, B2-STEP)

The harmonic oscillator `n = 1`, `χ = 0`, `H = I₀` (`cartAction 0`), `Nact = q₀`
(so `Nact(I) = I₀`), `P = 0`, `L = 1`: the identity `hid` and every majorant premise are
checked by kernel evaluation or `norm_num`, and the conclusion is the zero-drift statement.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

private theorem smoke_supBound_zero (P : CartPoly) (h : P = []) (r s : List ℚ) :
    cartSupBound P r s = 0 := by
  subst h; rfl

/-- Harmonic oscillator, `χ = 0`, `P = 0`, `L = 1`: zero action drift on `|t| ≤ 1`. -/
theorem stepSmoke_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (stepChartInv ([] : CartPoly) (5 : ℝ) (z t)).2
          (stepChartInv ([] : CartPoly) (5 : ℝ) (z t)).1 j -
        KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ 0 := by
  have hρl : ∀ i : Fin 1, (([5] : List ℚ).getD i 0 : ℚ) = (5 : ℝ) := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hrl : ∀ i : Fin 1, (([2] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (2 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hB : cartSupBound (cartAdPow ([] : CartPoly) 1 (cartAction 0)) [5] [5] = 0 :=
    smoke_supBound_zero _ rfl _ _
  have hBr : cartSupBound (cartBracket (cartAction 0) ([] : CartPoly)) [2] [2] = 0 :=
    smoke_supBound_zero _ rfl _ _
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := oscillatorStep_confinement
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
    (fun _ => by norm_num) w₀ hw₀
  refine ⟨z, fun t ht j => ?_⟩
  have := (hb t ht).2 j
  simpa using this.1

end KAM.EffectiveStability
