/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.PullbackNu
public import KAM.Wave.KamStep.StepLip
public import KAM.Wave.KamStep.StepPlus
public import KAM.Wave.KamStep.StepBracket
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The pull-back bound (blueprint-W `bpW:w5:pullback`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepPullback_bounds`: for the flow of two fields `Z₁, Z₂` (the parameters `ξ, ζ`) with
`|Z₁ - Z₂| ≤ N₁`, `16 M ≤ σ η²`, and fields `Y₁, Y₂` on `D(s-3σ, 4ηr)` with `|Y_i|_{ηr} ≤ Y₀`,
`|Y₁ - Y₂|_{ηr} ≤ Y_d`: the transported fields `y_i = (1 + N_i)⁻¹ Y_i(φ_i w)` on `D(s-5σ, ηr)`
satisfy
`ν(y₁) ≤ 2Y₀` and `ν(y₁ - y₂) ≤ 2Y_d + 8η⁻² N₁ Y₀/σ·… `
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η M : ℝ} [Fact (0 < r)]


theorem stepPullback_bounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)}
    (hF₁ : HomFieldBound_gen ha hp hpb r M FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r M FT₂)
    (hM0 : 0 < M) (hMs : 16 * M ≤ σ * η ^ 2) {N₁ : ℝ} (hN₁ : 0 ≤ N₁)
    (hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS ha hp hpb FT₁ r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N₁)
    {Y₁ Y₂ : KamPhase → KamPhase} {Y0 Yd : ℝ} (hY0 : 0 ≤ Y0)
    (hY₁ : DifferentiableOn ℂ Y₁ (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hY₂ : DifferentiableOn ℂ Y₂ (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hb₁ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)), kamNorm (η * r) (Y₁ z) ≤ Y0)
    (hb₂ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)), kamNorm (η * r) (Y₂ z) ≤ Y0)
    (hd : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)), kamNorm (η * r) (Y₁ z - Y₂ z) ≤ Yd)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {y₁ y₂ : StepPhase r}
    (hy₁ : y₁ + transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) t w y₁ =
      StepPhase.ofK (Y₁ (StepPhase.toK (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT₁ r)) t w))))
    (hy₂ : y₂ + transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r) t w y₂ =
      StepPhase.ofK (Y₂ (StepPhase.toK (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
        (stepFieldS ha hp hpb FT₂ r)) t w)))) :
    stepNu (η * r) y₁ ≤ 2 * Y0 ∧
      stepNu (η * r) (y₁ - y₂) ≤ 2 * (Yd + 2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * Y0 := by
  have hr : 0 < r := Fact.out
  set ι := stepEmbedCLM a p pb hpb r with hιdef
  have hρ : 0 < η * r := by positivity
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  have hMσ : M ≤ σ / 1024 := by nlinarith
  have hMδ : M < σ / 4 := by linarith
  have hF1 := stepFlowHyp_concrete' (S := s) ha hp hpb FT₁ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₁ hM0 hMδ
  have hF2 := stepFlowHyp_concrete' (S := s) ha hp hpb FT₂ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₂ hM0 hMδ
  have hVd : ∀ z ∈ stepDomain r (s - σ) r,
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ1 : DifferentiableOn ℂ (stepFieldS ha hp hpb FT₁ r) (stepDomain r (s - σ) r) :=
    (stepFieldS_differentiableOn_theta ha hp hpb FT₁).mono hVd
  have hZ2 : DifferentiableOn ℂ (stepFieldS ha hp hpb FT₂ r) (stepDomain r (s - σ) r) :=
    (stepFieldS_differentiableOn_theta ha hp hpb FT₂).mono hVd
  have hb1 : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT₁ r z‖ ≤ M := fun z hz =>
    stepFieldS_bound ha hp hpb FT₁ r hF₁ le_rfl hz
  have hb2 : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT₂ r z‖ ≤ M := fun z hz =>
    stepFieldS_bound ha hp hpb FT₂ r hF₂ le_rfl hz
  have hι : ∀ g, ‖ι g‖ ≤ ‖g‖ := norm_stepEmbedCLM_apply_le a p pb hpb r
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hball := stepDomain_U_margin hσ hσ1 (by linarith : 3 * σ < s) (hU'sub hw)
  have hρ' : 0 < σ / 8 := by positivity
  have hq : η⁻¹ ^ 2 * (M / (σ / 8)) ≤ 1 / 2 := by
    have : η⁻¹ ^ 2 * (M / (σ / 8)) = 8 * M / (σ * η ^ 2) := by field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  have hL : M / (σ / 4) ≤ 1 / 64 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  -- the images of the trajectories
  have himg : ∀ (Z : StepPhase r → StepPhase r)
      (h : FlowHyp (smoothField ι Z) (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2))
        M (σ / 4)),
      StepPhase.toK (holoFlow (smoothField ι Z) t w) ∈ kamDomain (s - 4 * σ) (2 * (η * r)) := by
    intro Z h
    have hdist := norm_holoFlow_sub_le h (hU'U hw) ht
    have hW : kamNorm r (StepPhase.toK (holoFlow (smoothField ι Z) t w) - StepPhase.toK w) ≤ M := by
      have : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
      have h2 : kamNorm r (StepPhase.toK (holoFlow (smoothField ι Z) t w) - StepPhase.toK w) =
          ‖holoFlow (smoothField ι Z) t w - w‖ := rfl
      rw [h2]
      exact hdist.trans (by nlinarith [h.M_pos])
    have : StepPhase.toK w + (StepPhase.toK (holoFlow (smoothField ι Z) t w) - StepPhase.toK w) ∈
        kamDomain (s - 4 * σ) (2 * η * r) :=
      stepImage_mem hr hσ hσ1 hη0 hη (by nlinarith : M ≤ σ * η ^ 2 / 16) hw hW
    have e : StepPhase.toK w + (StepPhase.toK (holoFlow (smoothField ι Z) t w) - StepPhase.toK w) =
        StepPhase.toK (holoFlow (smoothField ι Z) t w) := by rw [add_sub_cancel]
    rw [e] at this
    have e2 : 2 * η * r = 2 * (η * r) := by ring
    rw [e2] at this
    exact this
  have hmono : ∀ x, x ∈ kamDomain (s - 4 * σ) (2 * (η * r)) →
      x ∈ kamDomain (s - 3 * σ) (4 * (η * r)) := fun x hx =>
    kamDomain_mono (by linarith) (by positivity) (by nlinarith) hx
  have hx1 := himg _ hF1
  have hx2 := himg _ hF2
  have hc1 := hmono _ hx1
  have hc2 := hmono _ hx2
  have hu1 : stepNu (η * r) (StepPhase.ofK (r := r) (Y₁ (StepPhase.toK
      (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) t w)))) ≤ Y0 := hb₁ _ hc1
  have hsup := stepPullback_sup hη0 (by linarith) hι hF1 hZ1 hb1 hρ' hball hq ht hy₁
  refine ⟨hsup.trans (by linarith), ?_⟩
  have hsub := stepPullback_sub hη0 (by linarith) hι hF1 hF2 hZ1 hb1 hZ2 hb2 (by linarith)
    hN₁ hZZ hρ' hball hq ht hy₁ hy₂
  set φ₁ := holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) with hφ₁
  set φ₂ := holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) with hφ₂
  -- distance of the trajectories
  have hdist : ‖φ₁ t w - φ₂ t w‖ ≤ 2 * N₁ := by
    have hwU := hU'U hw
    have e1 := holoFlow_smooth_eq hF1 hZ1 hwU ht
    have e2 := holoFlow_smooth_eq hF2 hZ2 hwU ht
    have h3 := flowII_disp_sub hF1 hF2 hZ1 hZ2 hι hb2 hL hN₁ hZZ hwU ht
    have e3 : φ₁ t w - φ₂ t w = ι (smoothDisp ι (stepFieldS ha hp hpb FT₁ r) t w -
        smoothDisp ι (stepFieldS ha hp hpb FT₂ r) t w) := by
      rw [hφ₁, hφ₂, e1, e2, map_sub]; abel
    rw [e3]
    exact (hι _).trans h3
  have hνdist : kamNorm (η * r) (StepPhase.toK (φ₁ t w) - StepPhase.toK (φ₂ t w)) ≤
      η⁻¹ ^ 2 * (2 * N₁) := by
    have := (stepNu_mono (y := φ₁ t w - φ₂ t w) hη0 (by linarith)).2
    exact this.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
  have hlip := kamNorm_lipschitz_small (S := s - 3 * σ) (σ := σ) (ρ := η * r) (Y0 := Y0) hσ hσ1
    (by linarith) hρ hY₂ hb₂ hY0 (x := StepPhase.toK (φ₁ t w)) (x' := StepPhase.toK (φ₂ t w))
    (by rw [show s - 3 * σ - σ = s - 4 * σ by ring]; exact hx1)
    (by rw [show s - 3 * σ - σ = s - 4 * σ by ring]; exact hx2)
  have hu12 : stepNu (η * r) (StepPhase.ofK (r := r) (Y₁ (StepPhase.toK (φ₁ t w))) -
      StepPhase.ofK (r := r) (Y₂ (StepPhase.toK (φ₂ t w)))) ≤
      Yd + 2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁)) := by
    have e : stepNu (η * r) (StepPhase.ofK (r := r) (Y₁ (StepPhase.toK (φ₁ t w))) -
        StepPhase.ofK (r := r) (Y₂ (StepPhase.toK (φ₂ t w)))) =
        kamNorm (η * r) (Y₁ (StepPhase.toK (φ₁ t w)) - Y₂ (StepPhase.toK (φ₂ t w))) := rfl
    rw [e]
    have e2 : Y₁ (StepPhase.toK (φ₁ t w)) - Y₂ (StepPhase.toK (φ₂ t w)) =
        (Y₁ (StepPhase.toK (φ₁ t w)) - Y₂ (StepPhase.toK (φ₁ t w))) +
          (Y₂ (StepPhase.toK (φ₁ t w)) - Y₂ (StepPhase.toK (φ₂ t w))) := by abel
    rw [e2]
    refine (kamNorm_add_le hρ _ _).trans ?_
    have h4 := hd _ hc1
    have h5 : kamNorm (η * r) (Y₂ (StepPhase.toK (φ₁ t w)) - Y₂ (StepPhase.toK (φ₂ t w))) ≤
        2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁)) := by
      refine hlip.trans ?_
      have : Y0 / (σ / 2) = 2 * Y0 / σ := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hνdist (by positivity)
    linarith
  have hpos : 0 ≤ 4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) := by positivity
  calc _ ≤ _ := hsub
    _ ≤ 2 * (Yd + 2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * Y0 := by
      have := mul_le_mul_of_nonneg_left hu1 hpos
      nlinarith

end KAM.Wave
