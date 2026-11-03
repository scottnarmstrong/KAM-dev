/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain
public import KAM.EffectiveStability.OscillatorStep.Smoke

/-!
# One-step reduction and two-step smoke test (track B, B2-MULTI)

* `oscillatorStep_of_chain`: the one-step theorem `oscillatorStep_confinement` (with rational
  radii) follows from `oscillatorChain_confinement` applied to the one-element chain with
  `Q₁ := ∑_{j<L} (j!)⁻¹ ad_χ^j H`.
* `chainSmoke_zeroDrift`: two zero generators on the harmonic oscillator (`n = 1`,
  `H = I₀`, `Nact = q₀`, `P = 0`): every premise of `oscillatorChain_confinement` is checked by
  kernel evaluation or `norm_num`, and the conclusion is the zero-drift statement.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {n : ℕ}

/-- The one-step theorem for rational radii, derived from the chain theorem. -/
theorem oscillatorStep_of_chain {H χ Nact P : CartPoly}
    (hH : CartFits n H) (hχ : CartFits n χ) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    (hid : cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P) = true)
    {ρ δ ε : ℚ} {δc : ℝ} (hδ : 0 < δ) (hδc : 0 < δc) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hq : ∀ i : Fin n, cartSupBound (cartDq i χ) (List.replicate n ρ) (List.replicate n ρ) ≤
      ε * δ)
    (hp : ∀ i : Fin n, cartSupBound (cartDp i χ) (List.replicate n ρ) (List.replicate n ρ) ≤
      ε * δ)
    (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2)
    (hdom2 : ∀ i, r i + (δ : ℝ) < (ρ : ℝ))
    (hdom3 : ∀ i, r i + δc + (δ : ℝ) / 2 < (ρ : ℝ))
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * ((cartSupBound (cartAdPow χ L H) (List.replicate n ρ)
        (List.replicate n ρ) : ℚ) : ℝ) / ((L.factorial : ℝ) * δc))
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = stepChart χ (ρ : ℝ) w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = stepChart χ (ρ : ℝ) w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → stepChart χ (ρ : ℝ) (stepChartInv χ (ρ : ℝ) (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (stepChartInv χ (ρ : ℝ) (z t)).2
              (stepChartInv χ (ρ : ℝ) (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (stepChartInv χ (ρ : ℝ) (z t)).2
            (stepChartInv χ (ρ : ℝ) (z t)).1 j ≤ a j + η j * T := by
  have := oscillatorChain_confinement (H := H) (Nact := Nact) (P := P) hH hN hP hA
    (l := [⟨χ, cartLieSum χ H L, L, ρ, δ, ε⟩])
    ⟨⟨hδ, hε0, hε, hL, hχ, cartFits_lieSum hχ hH L, hq, hp⟩, Or.inl rfl, hid⟩ hδc a b η εb T
    hεb hT rl r hrl hr0 hdom1
    ⟨fun i => by simpa [oscTail] using hdom2 i, fun i => by simpa [oscTail] using hdom3 i,
      trivial⟩ hη
    (fun j => by
      refine (hdrift j).trans (le_of_eq ?_)
      simp only [oscChainBound]
      push_cast
      ring_nf)
    hmargin w₀ hw₀
  exact this

private theorem smoke_supBound_nil (P : CartPoly) (h : P = []) (r s : List ℚ) :
    cartSupBound P r s = 0 := by
  subst h; rfl

/-- Two zero generators on the harmonic oscillator: zero action drift on `|t| ≤ 1`. -/
theorem chainSmoke_zeroDrift (w₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (oscChainInv [(⟨[], cartAction 0, 1, 5, 1, 0⟩ : OscStep),
          ⟨[], cartAction 0, 1, 5, 1, 0⟩] (z t)).2
          (oscChainInv [(⟨[], cartAction 0, 1, 5, 1, 0⟩ : OscStep),
          ⟨[], cartAction 0, 1, 5, 1, 0⟩] (z t)).1 j -
        KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ 0 := by
  have hB : cartSupBound (cartAdPow ([] : CartPoly) 1 (cartAction 0))
      (List.replicate 1 (5 : ℚ)) (List.replicate 1 (5 : ℚ)) = 0 :=
    smoke_supBound_nil _ rfl _ _
  have hBr : cartSupBound (cartBracket (cartAction 0) ([] : CartPoly)) [2] [2] = 0 :=
    smoke_supBound_nil _ rfl _ _
  have hrl : ∀ i : Fin 1, (([2] : List ℚ).getD i 0 : ℚ) = (fun _ : Fin 1 => (2 : ℝ)) i := by
    intro i; obtain rfl := Subsingleton.elim i 0; norm_num
  have hstep : OscStepOK 1 (⟨[], cartAction 0, 1, 5, 1, 0⟩ : OscStep) :=
    ⟨by norm_num, le_rfl, by norm_num, le_rfl, cartFits_nil 1, cartFits_action Nat.zero_lt_one,
      fun i => by simp [cartDq, cartSupBound], fun i => by simp [cartDp, cartSupBound]⟩
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := oscillatorChain_confinement
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
    (fun _ => by norm_num) w₀ hw₀
  refine ⟨z, fun t ht j => ?_⟩
  have := (hb t ht).2 j
  simpa using this.1

end KAM.EffectiveStability
