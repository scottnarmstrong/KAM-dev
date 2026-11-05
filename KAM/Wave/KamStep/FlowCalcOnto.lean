/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealSmoothOnto
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Dφ^t(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}` (blueprint-W `bpW:w5:flow-calc` (iii))

The smoothing space `𝒫^{p_+}` is kept as its own representative space `G` with the inclusion
`ι : G →L F` (concretely `ι = stepEmbedCLM a p pb hpb r` on `StepPhase r`); it is never identified
with `𝒫` because the representative types coincide.

* `fderiv_holoFlow_smooth_targetUnit`: for a smoothing flow with `‖DΨ^t(w)‖ < 1`, there is a unit
  `T` of `G →L G` (`T = I + DΨ^t(w) ∘ ι`, a two-sided inverse in `G`) with
  `Dφ^t(w)(ι g) = ι (T g)` for every `g` (the target inverse, both identities from `Units`);
* `fderiv_holoFlow_smooth_image_range`: `Dφ^t(w) '' range ι = range ι`;
* `stepFlow_dPhi_targetUnit`, `stepFlow_dPhi_image_range`: the concrete flow of `X_F` on the small
  domain `D(s-3σ, r/4)`, every `t ∈ [-1, 1]`, with `ι = stepEmbedCLM` (generalizing the `t = 1`
  instances `StepCore.dPhi_smooth_onto` of W5-REAL, which are the special case `t = 1`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

section abstract

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}
  (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
  (hb : ∀ z ∈ V, ‖Z z‖ ≤ M)
include h hZ hb

/-- **Target inverse** (`bpW:w5:flow-calc` (iii)): `Dφ^t(w) ∘ ι = ι ∘ T` with `T` a unit of
`G →L G`. -/
theorem fderiv_holoFlow_smooth_targetUnit (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hD : ‖fderiv ℂ (smoothDisp ι Z t) w‖ < 1) :
    ∃ T : (G →L[ℂ] G)ˣ, ∀ g : G,
      fderiv ℂ (holoFlow (smoothField ι Z) t) w (ι g) = ι ((T : G →L[ℂ] G) g) := by
  set D : G →L[ℂ] G := (fderiv ℂ (smoothDisp ι Z t) w).comp ι with hDdef
  have hι1 : ‖ι‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by rw [one_mul]; exact hι x)
  have hTn : ‖-D‖ < 1 := by
    rw [norm_neg]
    calc ‖D‖ ≤ ‖fderiv ℂ (smoothDisp ι Z t) w‖ * ‖ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℂ (smoothDisp ι Z t) w‖ * 1 :=
          mul_le_mul_of_nonneg_left hι1 (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hD
  refine ⟨Units.oneSub (-D) hTn, fun g => ?_⟩
  rw [fderiv_holoFlow_smooth_mapsTo h hZ hb hw ht, Units.val_oneSub, sub_neg_eq_add]
  rfl

/-- **`Dφ^t(w)` maps `𝒫^{p_+}` onto itself** (`bpW:w5:flow-calc` (iii)):
`Dφ^t(w) '' range ι = range ι`. -/
theorem fderiv_holoFlow_smooth_image_range (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hD : ‖fderiv ℂ (smoothDisp ι Z t) w‖ < 1) :
    fderiv ℂ (holoFlow (smoothField ι Z) t) w '' range ι = range ι := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨_, (fderiv_holoFlow_smooth_mapsTo h hZ hb hw ht g).symm⟩
  · rintro ⟨g'', rfl⟩
    obtain ⟨g', hg'⟩ := fderiv_holoFlow_smooth_onto h hZ hb hι hw ht hD g''
    exact ⟨ι g', ⟨g', rfl⟩, hg'⟩

end abstract

section concrete

variable {a p pb s r σ Mf : ℝ} [Fact (0 < r)]

/-- The hypotheses of the abstract statements for the concrete flow of `X_F` on `D(s-3σ, r/4)`. -/
theorem stepFlow_dPhi_data (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    FlowHyp (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r))
        (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) Mf (σ / 4) ∧
      DifferentiableOn ℂ (stepFieldS ha hp hpb FT r) (stepDomain r (s - σ) r) ∧
      (∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf) ∧
      w ∈ stepDomain r (s - 2 * σ) (r / 2) ∧
      ‖fderiv ℂ (smoothDisp (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) t) w‖ < 1 := by
  have hMδ : Mf < σ / 4 := by linarith
  have hFl := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hVθ : stepDomain r (s - σ) r ⊆
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ := (stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVθ
  have hb : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf := fun z hz =>
    stepFieldS_bound ha hp hpb FT r hF le_rfl hz
  have hU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := stepDomain_mono' (by linarith)
    (by have := Fact.out (p := 0 < r); positivity)
    (by have := Fact.out (p := 0 < r); linarith) hw
  have hball := stepDomain_U_margin hσ hσ1 hσs hw
  have hD := flowII_deriv hFl hZ hb (by positivity : (0 : ℝ) < σ / 8) hball ht
  refine ⟨hFl, hZ, hb, hU, hD.trans_lt ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- **`DΦ^t` has a target inverse on `𝒫^{p_+}`** on `D(s-3σ, r/4)`, every `t ∈ [-1, 1]`
(`bpW:w5:flow-calc` (iii)): `Dφ^t(w) ∘ ι = ι ∘ T`, `T` a unit of `𝒫^{p_+} →L 𝒫^{p_+}`. -/
theorem stepFlow_dPhi_targetUnit (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∃ T : (StepPhase r →L[ℂ] StepPhase r)ˣ, ∀ g : StepPhase r,
      fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t) w
          (stepEmbedCLM a p pb hpb r g) =
        stepEmbedCLM a p pb hpb r ((T : StepPhase r →L[ℂ] StepPhase r) g) := by
  obtain ⟨hFl, hZ, hb, hU, hD⟩ := stepFlow_dPhi_data ha hp hpb hσ hσ1 hσs FT hF hMf0 hMf hw ht
  exact fderiv_holoFlow_smooth_targetUnit hFl hZ hb (norm_stepEmbedCLM_apply_le a p pb hpb r) hU ht
    hD

/-- **`DΦ^t(w)` maps `𝒫^{p_+}` onto `𝒫^{p_+}`** on `D(s-3σ, r/4)`, every `t ∈ [-1, 1]`
(`bpW:w5:flow-calc` (iii)): the image of `range ι` is `range ι`, `ι = stepEmbedCLM`. -/
theorem stepFlow_dPhi_image_range (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r)) t) w ''
        range (stepEmbedCLM a p pb hpb r) = range (stepEmbedCLM a p pb hpb r) := by
  obtain ⟨hFl, hZ, hb, hU, hD⟩ := stepFlow_dPhi_data ha hp hpb hσ hσ1 hσs FT hF hMf0 hMf hw ht
  exact fderiv_holoFlow_smooth_image_range hFl hZ hb (norm_stepEmbedCLM_apply_le a p pb hpb r) hU
    ht hD

end concrete

end KAM.Wave

end
