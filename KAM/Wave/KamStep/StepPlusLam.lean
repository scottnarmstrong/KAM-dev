/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusBound
public import KAM.Wave.KamStep.StepPlusArith
public import KAM.Wave.KamStep.TaylorFieldBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `λ`-bound of the field of `P_+` (blueprint-W `bpW:w5:step` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepPlus_pair_lamBound`: for two parameter values `ξ, ζ` (data indexed by `1, 2`, `d = |ξ - ζ|`)
of a
family with `|X_P| ≤ ε₀`, `|X_{P_1} - X_{P_2}| ≤ ε₁ d` on `D(s,r)`, `|X_F| ≤ M₀`, `|X_{F_1} -
X_{F_2}| ≤ M₁ d`,
`ε₀ + λε₁ ≤ ε`, `M₀ + λM₁ ≤ M_F`, `16M_F ≤ ση²`: `ν(X_{+,1}) ≤ S`, `ν(X_{+,1} - X_{+,2}) ≤ D d` with
`S + λ D ≤ 896ηε + 168 ε M_F/(ση²)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η : ℝ} [Fact (0 < r)]


/-- The sup constant of `X_+`. -/
def stepSplus (ε₀ M₀ η σ : ℝ) : ℝ :=
  2 * (128 * η * ε₀) + 2 * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ))

/-- The Lipschitz constant of `X_+`. -/
def stepDplus (ε₀ ε₁ M₀ M₁ η σ : ℝ) : ℝ :=
  (2 * (128 * η * ε₁ + 2 * (128 * η * ε₀) / σ * (η⁻¹ ^ 2 * (2 * M₁))) +
      4 * (η⁻¹ ^ 2 * (2 * M₁ / (σ / 8))) * (128 * η * ε₀)) +
    (2 * (η⁻¹ ^ 2 * (8 * (M₀ * (3 * ε₁) + 3 * ε₀ * M₁) / σ) +
      2 * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ)) / σ * (η⁻¹ ^ 2 * (2 * M₁))) +
    4 * (η⁻¹ ^ 2 * (2 * M₁ / (σ / 8))) * (η⁻¹ ^ 2 * (8 * (3 * ε₀) * M₀ / σ)))

theorem stepSplus_stepDplus_le {ε₀ ε₁ ε lam M₀ M₁ MF : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hlam : 0 ≤ lam) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hε : ε₀ + lam * ε₁ ≤ ε) (hM : M₀ + lam * M₁ ≤ MF) (hs : 16 * MF ≤ σ * η ^ 2) :
    stepSplus ε₀ M₀ η σ + lam * stepDplus ε₀ ε₁ M₀ M₁ η σ ≤
      896 * η * ε + 168 * ε * MF / (σ * η ^ 2) :=
  stepXplus_arith hσ hη hε₀ hε₁ hlam hM₀ hM₁ hε hM hs


theorem stepPlus_pair_lamBound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {P₁ P₂ : KamPhase → ℂ} {X₁ X₂ : KamPhase → KamPhase}
    (hP₁ : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P₁ X₁)
    (hP₂ : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P₂ X₂)
    (hper₁ : ∀ i, ∀ w ∈ kamDomain s r, P₁ (w + stepTau i) = P₁ w)
    (hper₂ : ∀ i, ∀ w ∈ kamDomain s r, P₂ (w + stepTau i) = P₂ w)
    {ε₀ ε₁ d M₀ M₁ : ℝ} (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁) (hd0 : 0 ≤ d) (hM0 : 0 < M₀)
    (hM₁ : 0 ≤ M₁)
    (hb₁ : ∀ z ∈ kamDomain s r, kamNorm r (X₁ z) ≤ ε₀)
    (hb₂ : ∀ z ∈ kamDomain s r, kamNorm r (X₂ z) ≤ ε₀)
    (hdiff : ∀ z ∈ kamDomain s r, kamNorm r (X₁ z - X₂ z) ≤ ε₁ * d)
    {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)}
    (hF₁ : HomFieldBound_gen ha hp hpb r M₀ FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r M₀ FT₂)
    (hΔF : HomFieldBound_gen ha hp hpb r (M₁ * d) (FT₁.homSub FT₂))
    {MF : ℝ} (hMs : 16 * MF ≤ σ * η ^ 2) (hMMF : M₀ ≤ MF)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    stepNu (η * r) (stepXplusS ha hp hpb X₁
        (stepTaylorOf ha hp hpb hs (Fact.out : 0 < r) hP₁ hper₁ hb₁) FT₁ w) ≤
        stepSplus ε₀ M₀ η σ ∧
      stepNu (η * r) (stepXplusS ha hp hpb X₁
          (stepTaylorOf ha hp hpb hs (Fact.out : 0 < r) hP₁ hper₁ hb₁) FT₁ w -
        stepXplusS ha hp hpb X₂ (stepTaylorOf ha hp hpb hs (Fact.out : 0 < r) hP₂ hper₂ hb₂)
          FT₂ w) ≤ stepDplus ε₀ ε₁ M₀ M₁ η σ * d := by
  have hr : 0 < r := Fact.out
  set T₁ := stepTaylorOf ha hp hpb hs hr hP₁ hper₁ hb₁ with hT₁def
  set T₂ := stepTaylorOf ha hp hpb hs hr hP₂ hper₂ hb₂ with hT₂def
  have hMs0 : 16 * M₀ ≤ σ * η ^ 2 := by linarith
  have hT₁ : HomFieldBound_gen ha hp hpb r (3 * ε₀) T₁ := stepTaylor_fieldBound ha hp hpb hs hr hP₁
      hper₁ hb₁
  have hT₂ : HomFieldBound_gen ha hp hpb r (3 * ε₀) T₂ := stepTaylor_fieldBound ha hp hpb hs hr hP₂
      hper₂ hb₂
  have hTn₁ := homNhat_fieldBound_gen ha hp hpb hr hs T₁ hT₁
  have hTn₂ := homNhat_fieldBound_gen ha hp hpb hr hs T₂ hT₂
  have hΔT : HomFieldBound_gen ha hp hpb r (3 * (ε₁ * d)) (T₁.homSub T₂) :=
    stepTaylor_subFieldBound ha hp hpb hs hr hP₁ hP₂ hper₁ hper₂ hb₁ hb₂ hdiff
  have hΔTn := homNhat_lipschitz_gen ha hp hpb hr hs T₁ T₂ hΔT
  have hY₁ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₁ z - stepField ha hp hpb T₁ z) ≤ 128 * η * ε₀ := by
    intro z hz
    have hz' : z ∈ kamDomain s (4 * η * r) := by
      have e : 4 * η * r = 4 * (η * r) := by ring
      rw [e]; exact kamDomain_mono (by linarith) (by positivity) le_rfl hz
    have hzs : z ∈ kamDomain s r := kamDomain_mono (by linarith) (by positivity)
      (by nlinarith) hz
    rw [stepField_taylorOf_eq ha hp hpb hs hr hP₁ hper₁ hb₁ hzs]
    exact taylorXR_remainder_128 hP₁.holoX hb₁ hr hη0 hη hz'
  have hY₂ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₂ z - stepField ha hp hpb T₂ z) ≤ 128 * η * ε₀ := by
    intro z hz
    have hz' : z ∈ kamDomain s (4 * η * r) := by
      have e : 4 * η * r = 4 * (η * r) := by ring
      rw [e]; exact kamDomain_mono (by linarith) (by positivity) le_rfl hz
    have hzs : z ∈ kamDomain s r := kamDomain_mono (by linarith) (by positivity)
      (by nlinarith) hz
    rw [stepField_taylorOf_eq ha hp hpb hs hr hP₂ hper₂ hb₂ hzs]
    exact taylorXR_remainder_128 hP₂.holoX hb₂ hr hη0 hη hz'
  have hYd : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) ((X₁ z - stepField ha hp hpb T₁ z) - (X₂ z - stepField ha hp hpb T₂ z)) ≤
        128 * η * (ε₁ * d) := by
    intro z hz
    have hz' : z ∈ kamDomain s (4 * η * r) := by
      have e : 4 * η * r = 4 * (η * r) := by ring
      rw [e]; exact kamDomain_mono (by linarith) (by positivity) le_rfl hz
    have hzs : z ∈ kamDomain s r := kamDomain_mono (by linarith) (by positivity)
      (by nlinarith) hz
    have h := taylorXR_remainder_128 (X := fun x => X₁ x - X₂ x)
      (hP₁.holoX.sub hP₂.holoX) hdiff hr hη0 hη hz'
    have hlin := taylorXR_sub hP₁.holoX hP₂.holoX hr hzs
    rw [hlin] at h
    rw [stepField_taylorOf_eq ha hp hpb hs hr hP₁ hper₁ hb₁ hzs,
      stepField_taylorOf_eq ha hp hpb hs hr hP₂ hper₂ hb₂ hzs]
    have e : (X₁ z - taylorXR X₁ z) - (X₂ z - taylorXR X₂ z) =
        (X₁ z - X₂ z) - (taylorXR X₁ z - taylorXR X₂ z) := by abel
    rw [e]; exact h
  have hdiffY₁ : DifferentiableOn ℂ (fun x => X₁ x - stepField ha hp hpb T₁ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))) := by
    have hsub : kamDomain (s - 3 * σ) (4 * (η * r)) ⊆ kamDomain s r := fun z hz =>
      kamDomain_mono (by linarith) (by positivity) (by nlinarith) hz
    exact (hP₁.holoX.mono hsub).sub (fun x hx =>
      (stepField_differentiableAt ha hp hpb T₁ (fun i => (hsub hx).1 i)).differentiableWithinAt)
  have hdiffY₂ : DifferentiableOn ℂ (fun x => X₂ x - stepField ha hp hpb T₂ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))) := by
    have hsub : kamDomain (s - 3 * σ) (4 * (η * r)) ⊆ kamDomain s r := fun z hz =>
      kamDomain_mono (by linarith) (by positivity) (by nlinarith) hz
    exact (hP₂.holoX.mono hsub).sub (fun x hx =>
      (stepField_differentiableAt ha hp hpb T₂ (fun i => (hsub hx).1 i)).differentiableWithinAt)
  have hΔ0 : 0 ≤ 3 * (ε₁ * d) := by positivity
  have hpair := stepXplus_pair_bound (e₁ := 3 * ε₀) (Δ₁ := 3 * (ε₁ * d)) (N₁ := M₁ * d)
    (Y0 := 128 * η * ε₀) (Yd := 128 * η * (ε₁ * d)) (Mf := M₀) ha hp hpb hσ hσ1 hσs hη0 hη
    (by positivity) hΔ0 (by positivity) (by positivity) hT₁ hT₂ hTn₁ hTn₂ hΔT hΔTn hF₁ hF₂ hΔF
    hM0 hMs0 hdiffY₁ hdiffY₂ hY₁ hY₂ hYd hw
  refine ⟨hpair.1.trans (le_of_eq ?_), hpair.2.trans (le_of_eq ?_)⟩
  · unfold stepSplus; ring
  · unfold stepDplus; ring

end KAM.Wave
