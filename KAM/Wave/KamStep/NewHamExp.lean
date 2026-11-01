/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Triangle
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The expansion of `H ∘ Φ` along the flow (`bpW:w5:new-ham`, step `n-exp`)

Scalar core, along one trajectory `t ↦ φ^t(w)`: let `n(t) = N(φ^t w)`, `ν(t) = N̂(φ^t w)`,
`ρ(t) = R(φ^t w)` with `n' = ν + â₀ - ρ` (flow-calc (v) with the bracket identity), `ν' = b_N`,
`ρ' = b_R` (the brackets `{N̂,F}`, `{R,F}` along the flow). Then
`n(1) = n(0) + ν(0) + â₀ - ρ(0) + ∫₀¹ (1-τ)(b_N - b_R)(τ) dτ` and `ρ(1) = ρ(0) + ∫₀¹ b_R`
(`stepExpansion`), hence `H(Φw) = N(w) + N̂(w) + â₀ + (P-R)(Φw) + ∫₀¹ ((1-τ) b_N + τ b_R)`
(`stepExpansion_H`).
-/

@[expose] public section

namespace KAM.Wave

open Set intervalIntegral

/-- FTC on `[0,1]` for a function with a continuous derivative within `[0,1]`. -/
theorem stepFTC {f f' : ℝ → ℂ} (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc 0 1) t)
    (hc : ContinuousOn f' (Icc 0 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ τ in (0 : ℝ)..t, f' τ = f t - f 0 := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  have hcf : ContinuousOn f (Icc 0 t) := fun x hx => (hd x (hsub hx)).continuousWithinAt.mono hsub
  refine integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcf (fun x hx => ?_) ?_
  · have hx1 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans_le ht.2⟩
    exact ((hd x ⟨hx1.1.le, hx1.2.le⟩).hasDerivAt (Icc_mem_nhds hx1.1 hx1.2)).hasDerivWithinAt
  · exact (hc.mono hsub).intervalIntegrable_of_Icc ht.1

theorem stepContOn {f f' : ℝ → ℂ} (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc 0 1) t)
    :
    ContinuousOn f (Icc 0 1) := fun t ht => (hd t ht).continuousWithinAt

/-- `∫₀¹ f = f(0) + ∫₀¹ (1-τ) f'(τ) dτ` (FTC twice, with the triangle integral). -/
theorem stepIntegral_eq {f f' : ℝ → ℂ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc 0 1) t)
    (hc : ContinuousOn f' (Icc 0 1)) :
    ∫ t in (0 : ℝ)..1, f t = f 0 + ∫ τ in (0 : ℝ)..1, (1 - τ) • f' τ := by
  have h1 : ∫ t in (0 : ℝ)..1, f t = ∫ t in (0 : ℝ)..1, (f 0 + ∫ τ in (0 : ℝ)..t, f' τ) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    simp only [stepFTC hd hc ht]; ring
  have hci : ContinuousOn (fun t => ∫ τ in (0 : ℝ)..t, f' τ) (Icc 0 1) := by
    have h : ContinuousOn (fun t => f t - f 0) (Icc 0 1) :=
      (stepContOn hd).sub continuousOn_const
    exact h.congr fun t ht => stepFTC hd hc ht
  rw [h1, integral_add intervalIntegrable_const (hci.intervalIntegrable_of_Icc zero_le_one),
    stepTriangle_on hc]
  simp

/-- **Expansion along the flow** (`n-exp`). -/
theorem stepExpansion {n nu rho bn br : ℝ → ℂ} {a0 : ℂ} (hbn : ContinuousOn bn (Icc 0 1))
    (hbr : ContinuousOn br (Icc 0 1))
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt n (nu t + a0 - rho t) (Icc 0 1) t)
    (hnu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt nu (bn t) (Icc 0 1) t)
    (hrho : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt rho (br t) (Icc 0 1) t) :
    n 1 = n 0 + nu 0 + a0 - rho 0 + ∫ τ in (0 : ℝ)..1, (1 - τ) • (bn τ - br τ) := by
  have hcn : ContinuousOn nu (Icc 0 1) := stepContOn hnu
  have hcr : ContinuousOn rho (Icc 0 1) := stepContOn hrho
  have hcc : ContinuousOn (fun t => nu t + a0 - rho t) (Icc 0 1) :=
    (hcn.add continuousOn_const).sub hcr
  have h1 := stepFTC hn hcc (t := 1) ⟨zero_le_one, le_rfl⟩
  have e1 := stepIntegral_eq hnu hbn
  have e2 := stepIntegral_eq hrho hbr
  have hi1 : IntervalIntegrable nu MeasureTheory.volume 0 1 := hcn.intervalIntegrable_of_Icc
      zero_le_one
  have hi2 : IntervalIntegrable rho MeasureTheory.volume 0 1 := hcr.intervalIntegrable_of_Icc
      zero_le_one
  have hs : ∫ t in (0 : ℝ)..1, (nu t + a0 - rho t) =
      (∫ t in (0 : ℝ)..1, nu t) + a0 - ∫ t in (0 : ℝ)..1, rho t := by
    rw [integral_sub (hi1.add intervalIntegrable_const) hi2, integral_add hi1
        intervalIntegrable_const]
    simp
  have hb1 : IntervalIntegrable (fun τ : ℝ => (1 - τ) • bn τ) MeasureTheory.volume 0 1 :=
    (((continuous_const.sub continuous_id).continuousOn.smul hbn)).intervalIntegrable_of_Icc
        zero_le_one
  have hb2 : IntervalIntegrable (fun τ : ℝ => (1 - τ) • br τ) MeasureTheory.volume 0 1 :=
    (((continuous_const.sub continuous_id).continuousOn.smul hbr)).intervalIntegrable_of_Icc
        zero_le_one
  have hsm : ∫ τ in (0 : ℝ)..1, (1 - τ) • (bn τ - br τ) =
      (∫ τ in (0 : ℝ)..1, (1 - τ) • bn τ) - ∫ τ in (0 : ℝ)..1, (1 - τ) • br τ := by
    rw [← integral_sub hb1 hb2]
    refine integral_congr fun τ _ => ?_
    simp [smul_sub]
  rw [hs, e1, e2] at h1
  rw [hsm]
  linear_combination (-1 : ℂ) * h1

/-- **`H ∘ Φ = N₊ + P₊ + â₀`, scalar form** (`n-exp`): with `p₁ = P(Φ w)`,
`n(1) + p₁ = n(0) + ν(0) + â₀ + (p₁ - ρ(1)) + ∫₀¹ ((1-τ) b_N + τ b_R)`. -/
theorem stepExpansion_H {n nu rho bn br : ℝ → ℂ} {a0 p1 : ℂ} (hbn : ContinuousOn bn (Icc 0 1))
    (hbr : ContinuousOn br (Icc 0 1))
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt n (nu t + a0 - rho t) (Icc 0 1) t)
    (hnu : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt nu (bn t) (Icc 0 1) t)
    (hrho : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt rho (br t) (Icc 0 1) t) :
    n 1 + p1 = n 0 + nu 0 + a0 + (p1 - rho 1) +
      ∫ τ in (0 : ℝ)..1, ((1 - τ) • bn τ + τ • br τ) := by
  have h := stepExpansion hbn hbr hn hnu hrho
  have hr := stepFTC hrho hbr (t := 1) ⟨zero_le_one, le_rfl⟩
  have hb1 : IntervalIntegrable (fun τ : ℝ => (1 - τ) • bn τ) MeasureTheory.volume 0 1 :=
    (((continuous_const.sub continuous_id).continuousOn.smul hbn)).intervalIntegrable_of_Icc
      zero_le_one
  have hb2 : IntervalIntegrable (fun τ : ℝ => (1 - τ) • br τ) MeasureTheory.volume 0 1 :=
    (((continuous_const.sub continuous_id).continuousOn.smul hbr)).intervalIntegrable_of_Icc
      zero_le_one
  have hb3 : IntervalIntegrable br MeasureTheory.volume 0 1 :=
    hbr.intervalIntegrable_of_Icc zero_le_one
  have hb4 : IntervalIntegrable (fun τ : ℝ => τ • br τ) MeasureTheory.volume 0 1 :=
    ((continuous_id.continuousOn.smul hbr)).intervalIntegrable_of_Icc zero_le_one
  have e1 : ∫ τ in (0 : ℝ)..1, (1 - τ) • (bn τ - br τ) =
      (∫ τ in (0 : ℝ)..1, (1 - τ) • bn τ) - ∫ τ in (0 : ℝ)..1, (1 - τ) • br τ := by
    rw [← integral_sub hb1 hb2]
    exact integral_congr fun τ _ => by simp [smul_sub]
  have e2 : ∫ τ in (0 : ℝ)..1, ((1 - τ) • bn τ + τ • br τ) =
      (∫ τ in (0 : ℝ)..1, (1 - τ) • bn τ) + ∫ τ in (0 : ℝ)..1, τ • br τ := by
    exact integral_add hb1 hb4
  have e3 : ∫ τ in (0 : ℝ)..1, br τ =
      (∫ τ in (0 : ℝ)..1, (1 - τ) • br τ) + ∫ τ in (0 : ℝ)..1, τ • br τ := by
    rw [← integral_add hb2 (hb4)]
    exact integral_congr fun τ _ => by simp [sub_smul]
  rw [e2]
  rw [e1] at h
  linear_combination h + (-1 : ℂ) * hr + e3

end KAM.Wave
