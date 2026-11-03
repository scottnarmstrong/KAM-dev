/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorStep.Remainder
public import KAM.EffectiveStability.Cauchy
public import KAM.EffectiveStability.Domains

/-!
# One-step normalization: the action-bracket bound (track B, B2-STEP)

`stepDrift_le`: for the chart remainder `R w = H (Ψ w) - N (I(w))` of the real flow `Ψ`,
`N I = Nact (I, 0)`, and a real point `x` of the closed oscillator domain,
`|q_j ∂_{p_j} R - p_j ∂_{q_j} R| ≤ η j`. The proof splits `R = P + Re Rem ∘ ι` near `x` (the exact
Lie-sum identity), bounds the polynomial part by `cartSupBound` and the holomorphic remainder by
the Cauchy estimate on the polydisc of radius `δc`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical Filter
open scoped Topology

namespace KAM.EffectiveStability

open CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]

/-- Differentiability of the real part of a holomorphic function along the real slice. -/
theorem differentiableAt_realPart {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : KAM.realInclusion₂ n x ∈ U) :
    DifferentiableAt ℝ (fun y => (f (KAM.realInclusion₂ n y)).re) x := by
  have hd := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have h1 := hd.restrictScalars ℝ
  exact ((Complex.reCLM.hasFDerivAt (x := f (KAM.realInclusion₂ n x))).comp x
    (h1.comp x (KAM.realInclusion₂ n).hasFDerivAt)).differentiableAt

omit [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The chart remainder `R` is `P + Re Rem ∘ ι` on the real half interior. -/
theorem chartRemainder_eq {χ H Nact P : CartPolyK K} (hN : CartFits n Nact)
    (hA : cartActOnly Nact = true) {L : ℕ} {ρ δ ε : ℝ} {hδ : 0 < δ}
    (hid : cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P) = true)
    (hS : SmallField (gaugeScalar δ hδ) (cpolyOpen ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) ε)
    {y : (Fin n → ℝ) × (Fin n → ℝ)}
    (hy : y ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2)) :
    cartEval H (realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1 y) -
        cartEval Nact ((KAM.Planetary.oscillatorAction y.2 y.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ)) =
      cartEval P y + (stepRem χ H ρ L (KAM.realInclusion₂ n y)).re := by
  rw [stepRem_realInclusion₂ hS L hy, Complex.ofReal_re]
  have h := cartEval_eq_of_eqCheck (R := ℝ) hid y
  rw [cartEval_add, cartEval_actSubst_real Nact hN hA] at h
  rw [h]
  ring

/-- **Drift bound** for the chart remainder at a real point of the closed oscillator domain. -/
theorem stepDrift_le {χ H Nact P : CartPolyK K} (hχ : CartFits n χ) (hH : CartFits n H)
    (hN : CartFits n Nact) (hP : CartFits n P) (hA : cartActOnly Nact = true) {L : ℕ}
    (hL : 1 ≤ L) {ρ δ δc ε : ℝ} {hδ : 0 < δ} (hδc : 0 < δc)
    (hid : cartEqCheck (cartLieSum χ H L) (cartAdd (cartActSubst Nact) P) = true)
    (hS : SmallField (gaugeScalar δ hδ) (cpolyOpen ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) ε)
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    (rl : List ℚ) (r b η : Fin n → ℝ) (hrl : ∀ i : Fin n, ((rl.getD i 0 : ℚ) : ℝ) = r i)
    (hr0 : ∀ i, 0 ≤ r i) (hb : ∀ i, 2 * b i ≤ r i ^ 2) (hr3 : ∀ i, r i + δc + δ / 2 < ρ)
    (hdrift : ∀ j : Fin n, ((cartSupBound (cartBracket (cartAction j) P) rl rl : ℚ) : ℝ) ≤
      η j - 2 * r j * ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) /
        ((L.factorial : ℝ) * δc))
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ j, KAM.Planetary.oscillatorAction x.2 x.1 j ≤ b j)
    (hxI : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2)) (j : Fin n) :
    |x.1 j * fderiv ℝ (fun w => cartEval H (realFlow
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1 w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) x (0, Pi.single j 1) -
      x.2 j * fderiv ℝ (fun w => cartEval H (realFlow
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1 w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) x (Pi.single j 1, 0)| ≤ η j := by
  set B : ℝ := ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) with hB
  set U := gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2) with hU
  have hUo : IsOpen U := isOpen_gaugeInterior hS.isOpen _ _
  have hdiffR := differentiableOn_stepRem (χ := χ) (H := H) hS L
  have hxU : KAM.realInclusion₂ n x ∈ U := hxI
  -- local decomposition
  have hev : (fun w => cartEval H (realFlow
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1 w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) =ᶠ[𝓝 x]
      fun y => cartEval P y + (stepRem χ H ρ L (KAM.realInclusion₂ n y)).re := by
    filter_upwards [(isOpen_realInterior hS.isOpen (1 / 2)).mem_nhds hxI] with y hy
    exact chartRemainder_eq hN hA hid hS hy
  have hdP : DifferentiableAt ℝ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => cartEval P y) x :=
    ((contDiff_eval (𝕜 := ℝ) P 1).differentiable one_ne_zero).differentiableAt
  have hdRe := differentiableAt_realPart hUo hdiffR hxU
  have hfd : ∀ v, fderiv ℝ (fun w => cartEval H (realFlow
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) (cpolyOpen ρ) 1 w) -
        cartEval Nact ((KAM.Planetary.oscillatorAction w.2 w.1, (0 : Fin n → ℝ)) :
          (Fin n → ℝ) × (Fin n → ℝ))) x v =
      fderiv ℝ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => cartEval P y) x v +
        fderiv ℝ (fun y => (stepRem χ H ρ L (KAM.realInclusion₂ n y)).re) x v := by
    intro v
    rw [hev.fderiv_eq, fderiv_fun_add hdP hdRe]
    rfl
  rw [hfd, hfd, fderiv_eval_p, fderiv_eval_q]
  have hxr : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i := fun i =>
    CartPoly.abs_le_of_oscillatorAction_le x b r i (hx i) (hb i) (hr0 i)
  have hpoly := CartPoly.abs_actionBracket_le_supBound P hP j rl x
    (fun i => by rw [hrl]; exact (hxr i).1) (fun i => by rw [hrl]; exact (hxr i).2)
  have hsub : cpolydisc (KAM.realInclusion₂ n x) δc ⊆ U :=
    cauchyDisc_subset_gaugeInterior hδ hr3 hxr
  have hM : ∀ w ∈ cpolydisc (KAM.realInclusion₂ n x) δc,
      ‖stepRem χ H ρ L w‖ ≤ B / (L.factorial : ℝ) := fun w hw =>
    norm_stepRem_le hχ hH hS ρl hρl hL (hsub hw)
  have hcau := abs_actionBracket_le_of_cauchy hUo hdiffR hxU hδc hsub hM j
  have hM0 : 0 ≤ B / (L.factorial : ℝ) / δc := by
    refine div_nonneg (le_trans (norm_nonneg _) (hM (KAM.realInclusion₂ n x) ?_)) hδc.le
    intro i
    simp [hδc.le]
  have hxj : |x.1 j| + |x.2 j| ≤ 2 * r j := by linarith [(hxr j).1, (hxr j).2]
  have hcau' : (|x.1 j| + |x.2 j|) * (B / (L.factorial : ℝ) / δc) ≤
      2 * r j * B / ((L.factorial : ℝ) * δc) := by
    calc _ ≤ 2 * r j * (B / (L.factorial : ℝ) / δc) := mul_le_mul_of_nonneg_right hxj hM0
      _ = _ := by rw [div_div]; ring
  have e : x.1 j * (cartEval (cartDp j P) x + fderiv ℝ (fun y => (stepRem χ H ρ L
        (KAM.realInclusion₂ n y)).re) x (0, Pi.single j 1)) -
      x.2 j * (cartEval (cartDq j P) x + fderiv ℝ (fun y => (stepRem χ H ρ L
        (KAM.realInclusion₂ n y)).re) x (Pi.single j 1, 0)) =
      (x.1 j * cartEval (cartDp j P) x - x.2 j * cartEval (cartDq j P) x) +
      (x.1 j * fderiv ℝ (fun y => (stepRem χ H ρ L (KAM.realInclusion₂ n y)).re) x
        (0, Pi.single j 1) - x.2 j * fderiv ℝ (fun y => (stepRem χ H ρ L
          (KAM.realInclusion₂ n y)).re) x (Pi.single j 1, 0)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have := hdrift j
  linarith

end KAM.EffectiveStability
