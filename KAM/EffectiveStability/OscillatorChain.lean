/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChain.Drift
public import KAM.EffectiveStability.Oscillator

/-!
# `m`-generator finite Birkhoff normalization ⇒ certified oscillator confinement (track B, B2-MULTI)

`oscillatorChain_confinement`: the soundness theorem of the checker for a FINITE LIST of
generators `χ₁, …, χ_m` (`OscStep`, outermost first), generalizing `oscillatorStep_confinement`.
The chart is `Ψ = Φ₁ ∘ ⋯ ∘ Φ_m` (`oscChainMap`), each `Φ_k` the real time-one flow of `χ_k` on
`cpolyOpen ρ_k`; `Ψinv` is the reversed composition of time `-1` flows (`oscChainInv`).

Premises (all finite data, exact `Bool` checks or inequalities between `ℚ`-computable
majorants; none mentions a flow, a remainder or confinement):

* `OscChainOK n Nact P l H`: per-step small-field majorants and typing, the exact identities
  `cartEqCheck (cartLieSum χ_k Q_{k-1} L_k) Q_k = true` and
  `cartEqCheck Q_m (Nact(I) + P) = true`;
* `OscDomOK n r δc l`: the radius budget `r_i + (inner displacement) + δ_k < ρ_k` (real chart
  domain) and `r_i + δc + (inner displacement) + δ_k / 2 < ρ_k` (Cauchy discs);
* the drift inequality `cartSupBound {I_j, P} r ≤ η_j - 2 r_j (∑_k B_k / L_k!) / δc`.

The conclusion is that of `oscillator_confinement` for `V = univ` and the physical Hamiltonian
`H.cartEval`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {n : ℕ}

theorem osc_subset_oscBox {b r : Fin n → ℝ} {εb : ℝ} (hb : ∀ i, 2 * (b i + εb) ≤ r i ^ 2)
    (hr0 : ∀ i, 0 ≤ r i) : osc (fun j => b j + εb) ⊆ oscBox r 0 := by
  intro w hw i
  have hi := hw i
  simp only [KAM.Planetary.oscillatorAction] at hi
  have hbi := hb i
  constructor
  · exact (abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w.2 i)]) (hr0 i)).trans_eq (by ring)
  · exact (abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w.1 i)]) (hr0 i)).trans_eq (by ring)

/-- **`m`-generator soundness** (track B, B2-MULTI): finitely many exact Lie-sum identities plus
rational/real majorant inequalities certify oscillator confinement for the physical flow. -/
theorem oscillatorChain_confinement {H Nact P : CartPoly}
    (hH : CartFits n H) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {l : List OscStep} (hok : OscChainOK n Nact P l H)
    {δc : ℝ} (hδc : 0 < δc) (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom : OscDomOK n r δc l)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * (oscChainBound n l H : ℝ) / δc)
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = oscChainMap l w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = oscChainMap l w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → oscChainMap l (oscChainInv l (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (oscChainInv l (z t)).2
              (oscChainInv l (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (oscChainInv l (z t)).2
            (oscChainInv l (z t)).1 j ≤ a j + η j * T := by
  have hl := hok.stepsOK
  have hDsub : osc (fun j => b j + εb) ⊆ oscBox r 0 := osc_subset_oscBox hdom1 hr0
  have hΨ : IsCanonicalChart (oscChainMap l) (oscChainInv l) (osc (fun j => b j + εb)) univ :=
    (oscChain_isCanonical hl hdom).mono_chart (isOpen_osc _) hDsub (subset_univ _)
  have hHΨ : ContDiffOn ℝ 2 (fun w => cartEval H (oscChainMap l w)) (osc (fun j => b j + εb)) :=
    (contDiff_eval (𝕜 := ℝ) H 2).comp_contDiffOn hΨ.chart_smooth
  have hNd : Differentiable ℝ (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
      cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
        (Fin n → ℝ) × (Fin n → ℝ))) :=
    ((contDiff_eval (𝕜 := ℝ) Nact 1).comp
      ((contDiff_oscAct (n := n)).of_le le_top |>.prodMk contDiff_const)).differentiable
      one_ne_zero
  exact oscillator_confinement a b η εb T hεb hT hη hmargin univ isOpen_univ
    (fun w => cartEval H w) ((contDiff_eval (𝕜 := ℝ) H 2).contDiffOn)
    (oscChainMap l) (oscChainInv l) hΨ.chart_smooth (fun _ _ => mem_univ _) hΨ.chart_symp
    hΨ.chart_leftInv
    (fun I => cartEval Nact ((I, (0 : Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ)))
    (fun w => cartEval H (oscChainMap l w) -
      cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
        (Fin n → ℝ) × (Fin n → ℝ)))
    (hHΨ.differentiableOn (by norm_num) |>.sub hNd.differentiableOn)
    (fun w _ => by ring)
    (fun w hw j => chainDrift_le hH hN hP hA hok hdom hδc rl b η hrl hr0 hdom1 hεb hdrift hw j)
    w₀ hw₀

end KAM.EffectiveStability
