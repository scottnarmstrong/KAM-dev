/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusLam
public import KAM.Wave.KamStep.ZeroTaylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `λ`-bound of `X_+` as a family bound (blueprint-W `bpW:w5:step` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepTaylorFam`: the family `ξ ↦ R_ξ` (`stepTaylorOf` on the parameter set, `zeroTaylor` off it).
`stepPlus_famBound`: `FamBound` of `X_+` on `D(s-5σ, ηr)` in the norm at scale `ηr`, with the
constant
`896ηε + 168 ε M_F/(ση²)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η : ℝ} [Fact (0 < r)]

open Classical in
/-- The family of Taylor elements: `stepTaylorOf` on the parameter set, zero off it. -/
def stepTaylorFam (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (Par : Set (Fin 2 → ℝ)) (P : (Fin 2 → ℝ) → KamPhase → ℂ) (X : (Fin 2 → ℝ) → KamPhase → KamPhase)
    {ε₀ : ℝ}
    (hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) (P ξ) (X ξ))
    (hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀)
    (ξ : Fin 2 → ℝ) : HomTaylor_gen a p pb s :=
  if h : ξ ∈ Par then stepTaylorOf ha hp hpb hs hr (hP ξ h) (hper ξ h) (hb ξ h)
  else zeroTaylor a p pb s

theorem stepTaylorFam_of_mem (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    {Par : Set (Fin 2 → ℝ)} {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
    {ε₀ : ℝ} (hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r)
      (P ξ) (X ξ))
    (hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    stepTaylorFam ha hp hpb hs hr Par P X hP hper hb ξ =
      stepTaylorOf ha hp hpb hs hr (hP ξ hξ) (hper ξ hξ) (hb ξ hξ) := by
  classical
  simp [stepTaylorFam, hξ]

/-- **The family bound of `X_+`** (`bpW:w5:step` (ii), `(6)`: `|X_{P_+}|^λ_{ηr,D_+} ≤
896ηε + 168 ε M_F/(ση²)`). -/
theorem stepPlus_famBound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {Par : Set (Fin 2 → ℝ)} {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
    {lam ε ε₀ ε₁ M₀ M₁ MF : ℝ} (hlam : 0 ≤ lam)
    (hP : ∀ ξ ∈ Par, IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) (P ξ) (X ξ))
    (hper : ∀ ξ ∈ Par, ∀ i, ∀ w ∈ kamDomain s r, P ξ (w + stepTau i) = P ξ w)
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hM0 : 0 < M₀) (hM₁ : 0 ≤ M₁)
    (hb : ∀ ξ ∈ Par, ∀ z ∈ kamDomain s r, kamNorm r (X ξ z) ≤ ε₀)
    (hdiff : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ z ∈ kamDomain s r,
      kamNorm r (X ξ z - X ζ z) ≤ ε₁ * ‖ξ - ζ‖)
    (hε : ε₀ + lam * ε₁ ≤ ε) (hM : M₀ + lam * M₁ ≤ MF)
    (FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ))
    (hF : ∀ ξ ∈ Par, HomFieldBound_gen ha hp hpb r M₀ (FT ξ))
    (hFL : ∀ ξ ∈ Par, ∀ ζ ∈ Par,
      HomFieldBound_gen ha hp hpb r (M₁ * ‖ξ - ζ‖) ((FT ξ).homSub (FT ζ)))
    (hMs : 16 * MF ≤ σ * η ^ 2) :
    FamBound Par (kamDomain (s - 5 * σ) (η * r)) (η * r) lam
      (896 * η * ε + 168 * ε * MF / (σ * η ^ 2))
      (fun ξ w => StepPhase.toK (stepXplusS (r := r) ha hp hpb (X ξ)
        (stepTaylorFam ha hp hpb hs Fact.out Par P X hP hper hb ξ) (FT ξ)
        (StepPhase.ofK (r := r) w))) := by
  have hr : 0 < r := Fact.out
  have hMMF : M₀ ≤ MF := by nlinarith [mul_nonneg hlam hM₁]
  refine ⟨stepSplus ε₀ M₀ η σ, stepDplus ε₀ ε₁ M₀ M₁ η σ, ?_, ?_, ?_, ?_, ?_⟩
  · unfold stepSplus; positivity
  · unfold stepDplus; positivity
  · exact (stepSplus_stepDplus_le hσ hη0 hε₀ hε₁ hlam hM0.le hM₁ hε hM hMs)
  · intro ξ hξ w hw
    have := (stepPlus_pair_lamBound ha hp hpb hs hσ hσ1 hσs hη0 hη (hP ξ hξ) (hP ξ hξ)
      (hper ξ hξ) (hper ξ hξ) hε₀ hε₁ (norm_nonneg (ξ - ξ)) hM0 hM₁ (hb ξ hξ) (hb ξ hξ)
      (hdiff ξ hξ ξ hξ) (hF ξ hξ) (hF ξ hξ) (hFL ξ hξ ξ hξ) hMs hMMF
      (w := StepPhase.ofK (r := r) w) hw).1
    beta_reduce
    rw [stepTaylorFam_of_mem ha hp hpb hs hr hP hper hb hξ]
    exact this
  · intro ξ hξ ζ hζ w hw
    have := (stepPlus_pair_lamBound ha hp hpb hs hσ hσ1 hσs hη0 hη (hP ξ hξ) (hP ζ hζ)
      (hper ξ hξ) (hper ζ hζ) hε₀ hε₁ (norm_nonneg (ξ - ζ)) hM0 hM₁ (hb ξ hξ) (hb ζ hζ)
      (hdiff ξ hξ ζ hζ) (hF ξ hξ) (hF ζ hζ) (hFL ξ hξ ζ hζ) hMs hMMF
      (w := StepPhase.ofK (r := r) w) hw).2
    beta_reduce
    rw [stepTaylorFam_of_mem ha hp hpb hs hr hP hper hb hξ,
      stepTaylorFam_of_mem ha hp hpb hs hr hP hper hb hζ]
    exact this

end KAM.Wave
