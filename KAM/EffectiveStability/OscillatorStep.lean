/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorStep.Drift
public import KAM.EffectiveStability.Oscillator

/-!
# One-step finite Birkhoff normalization ⇒ certified oscillator confinement (track B, B2-STEP)

`oscillatorStep_confinement`: the soundness theorem of the checker for ONE generator `χ`. Every
premise is finite data (polynomials with `ℚ` coefficients, radii lists) or a real inequality between
`ℚ`-computable majorants; no premise mentions the flow, the remainder, or confinement.

* `hid`: the exact identity `∑_{j<L} (j!)⁻¹ ad_χ^j H = Nact(I) + P` (`cartEqCheck`), where `Nact`
  involves the `q`-variables only (`cartActOnly`) and is evaluated at the oscillator actions;
* `hq`, `hp`: majorants `cartSupBound (∂χ) ρ ≤ ε δ` (small field of the generator on `cpolyOpen ρ`);
* domain inequalities (chart domain, Cauchy discs) and the drift inequality
  `cartSupBound {I_j, P} r ≤ η_j - 2 r_j B / (L! δc)`, `B = cartSupBound (ad_χ^L H) ρ`.

The conclusion is that of `oscillator_confinement` for `V = univ`, the physical Hamiltonian
`H.cartEval`, and the chart `Ψ = realFlow φ Ω 1` of the time-one map of the complexified generator.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The chart `Ψ`: the real time-one map of the flow of the complexified generator `χ` on the
open polydisc `cpolyOpen ρ`. -/
def stepChart (χ : CartPolyK K) (ρ : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The inverse chart `Ψinv`: the real time-`(-1)` map. -/
def stepChartInv (χ : CartPolyK K) (ρ : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) (-1)

/-- **One-step soundness** (track B, B2-STEP): a single exact finite Lie-sum identity plus
rational/real majorant inequalities certify oscillator confinement for the physical flow. -/
theorem oscillatorStep_confinement {H χ Nact P : CartPolyK K}
    (hH : CartFits n H) (hχ : CartFits n χ) (hN : CartFits n Nact) (hP : CartFits n P)
    (hA : cartActOnly Nact = true) {L : ℕ} (hL : 1 ≤ L)
    (hid : cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P) = true)
    {ρ δ δc ε : ℝ} (hδ : 0 < δ) (hδc : 0 < δc) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (a b η : Fin n → ℝ) (εb T : ℝ) (hεb : 0 < εb) (hT : 0 ≤ T)
    (rl : List ℚ) (r : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hdom1 : ∀ i, 2 * (b i + εb) ≤ r i ^ 2) (hdom2 : ∀ i, r i + δ < ρ)
    (hdom3 : ∀ i, r i + δc + δ / 2 < ρ)
    (hη : ∀ j, 0 ≤ η j)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) /
        ((L.factorial : ℝ) * δc))
    (hmargin : ∀ j, a j + T * η j < b j)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ a j) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = stepChart χ ρ w₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, z t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
        HasDerivAt z (KAM.hamiltonianVectorField
          (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = stepChart χ ρ w₀ →
        (∀ t ∈ I, y t ∈ (univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) ∧
          HasDerivAt y (KAM.hamiltonianVectorField
            (fun w : (Fin n → ℝ) × (Fin n → ℝ) => cartEval H w) (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ T → stepChart χ ρ (stepChartInv χ ρ (z t)) = z t ∧
        ∀ j, |KAM.Planetary.oscillatorAction (stepChartInv χ ρ (z t)).2
              (stepChartInv χ ρ (z t)).1 j -
            KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ η j * |t| ∧
          KAM.Planetary.oscillatorAction (stepChartInv χ ρ (z t)).2
            (stepChartInv χ ρ (z t)).1 j ≤ a j + η j * T := by
  have hS := smallField_of_supBound hχ hδ ρl hρl hε0 hε hq hp
  have hφ := differentiableOn_cartEval (n := n) χ (cpolyOpen ρ)
  have hreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ cpolyOpen ρ →
      (cartEval χ (KAM.realInclusion₂ n x)).im = 0 := fun x _ => cartEval_realInclusion₂_im χ x
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hDsub : osc (fun j => b j + εb) ⊆ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1 :=
    osc_subset_realInterior hδ hdom1 hr0 hdom2
  have hDsub2 : osc (fun j => b j + εb) ⊆ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2) :=
    hDsub.trans (realInterior_mono (by norm_num))
  have hb2 : ∀ i, 2 * b i ≤ r i ^ 2 := fun i => by linarith [hdom1 i]
  have hΨ : ContDiffOn ℝ 2 (stepChart χ ρ) (osc (fun j => b j + εb)) :=
    ((contDiffOn_realFlow hS h1).of_le (WithTop.coe_le_coe.2 le_top)).mono hDsub2
  have hHΨ : ContDiffOn ℝ 2 (fun w => cartEval H (stepChart χ ρ w)) (osc (fun j => b j + εb)) :=
    (contDiff_eval (𝕜 := ℝ) H 2).comp_contDiffOn hΨ
  have hNd : Differentiable ℝ (fun w : (Fin n → ℝ) × (Fin n → ℝ) =>
      cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
        (Fin n → ℝ) × (Fin n → ℝ))) :=
    ((contDiff_eval (𝕜 := ℝ) Nact 1).comp
      ((contDiff_oscAct (n := n)).of_le le_top |>.prodMk contDiff_const)).differentiable
      one_ne_zero
  exact oscillator_confinement a b η εb T hεb hT hη hmargin univ isOpen_univ
    (fun w => cartEval H w) ((contDiff_eval (𝕜 := ℝ) H 2).contDiffOn)
    (stepChart χ ρ) (stepChartInv χ ρ) hΨ (fun _ _ => mem_univ _)
    (fun w hw u v => realFlow_symplectic hφ hS hreal h1 (hDsub2 hw) u v)
    (fun w hw => realFlow_neg_realFlow_one hS.isOpen hφ hS hreal (hDsub hw))
    (fun I => cartEval Nact ((I, (0 : Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ)))
    (fun w => cartEval H (stepChart χ ρ w) -
      cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
        (Fin n → ℝ) × (Fin n → ℝ)))
    (hHΨ.differentiableOn (by norm_num) |>.sub hNd.differentiableOn)
    (fun w _ => by ring)
    (fun w hw j => stepDrift_le hχ hH hN hP hA hL hδc hid hS ρl hρl rl r b η hrl hr0 hb2
      hdom3 hdrift hw
      (oscClosed_subset_realInterior hδ hb2 hr0 hdom2 hw |> fun h => realInterior_mono
        (by norm_num) h) j)
    w₀ hw₀

end KAM.EffectiveStability
