/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusAssemble
public import KAM.Wave.KamStep.StepPullbackBound
public import KAM.Wave.KamStep.StepNuIntegral
public import KAM.Wave.KamStep.StepBracket
public import KAM.Wave.KamStep.StepPlusClass
public import KAM.Wave.KamStep.StepCtx
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounds of the field of `P_+` (blueprint-W `bpW:w5:new-ham` (ii), `bpW:w5:step` (ii))

-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf e₁ : ℝ} [Fact (0 < r)]

/-- **The pulled-back term**: bounds of `y_A = (1 + N_1)⁻¹ (X_P - X_R)(Φ w)` for two parameters. -/
theorem stepXplusA_bounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {X₁ X₂ : KamPhase → KamPhase} {T₁ T₂ : HomTaylor_gen a p pb s}
    {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)}
    (hF₁ : HomFieldBound_gen ha hp hpb r Mf FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r Mf FT₂)
    (hM0 : 0 < Mf) (hMs : 16 * Mf ≤ σ * η ^ 2) {N₁ : ℝ} (hN₁ : 0 ≤ N₁)
    (hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS ha hp hpb FT₁ r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N₁)
    {Y0 Yd : ℝ} (hY0 : 0 ≤ Y0)
    (hY₁ : DifferentiableOn ℂ (fun x => X₁ x - stepField ha hp hpb T₁ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hY₂ : DifferentiableOn ℂ (fun x => X₂ x - stepField ha hp hpb T₂ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hb₁ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₁ z - stepField ha hp hpb T₁ z) ≤ Y0)
    (hb₂ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₂ z - stepField ha hp hpb T₂ z) ≤ Y0)
    (hd : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) ((X₁ z - stepField ha hp hpb T₁ z) - (X₂ z - stepField ha hp hpb T₂ z)) ≤ Yd)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    let ι := stepEmbedCLM a p pb hpb r
    stepNu (η * r) (transSolve (transNop ι (stepFieldS ha hp hpb FT₁ r) 1 w)
        (stepXPS X₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w)))
      ≤ 2 * Y0 ∧
    stepNu (η * r) (transSolve (transNop ι (stepFieldS ha hp hpb FT₁ r) 1 w)
        (stepXPS X₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w)) -
      transSolve (transNop ι (stepFieldS ha hp hpb FT₂ r) 1 w)
        (stepXPS X₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w) -
          stepFieldS ha hp hpb T₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w)))
      ≤ 2 * (Yd + 2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * Y0 := by
  intro ι
  have hr : 0 < r := Fact.out
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  have hMσ : Mf ≤ σ / 1024 := by nlinarith
  have hMδ : Mf < σ / 4 := by linarith
  have hF1 := stepFlowHyp_concrete' (S := s) ha hp hpb FT₁ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₁ hM0 hMδ
  have hF2 := stepFlowHyp_concrete' (S := s) ha hp hpb FT₂ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₂ hM0 hMδ
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hq1 : ‖transNop ι (stepFieldS ha hp hpb FT₁ r) 1 w‖ < 1 :=
    lt_of_le_of_lt (stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF₁ hM0 hMσ (hU'sub hw)
      ⟨by norm_num, le_rfl⟩) (by norm_num)
  have hq2 : ‖transNop ι (stepFieldS ha hp hpb FT₂ r) 1 w‖ < 1 :=
    lt_of_le_of_lt (stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF₂ hM0 hMσ (hU'sub hw)
      ⟨by norm_num, le_rfl⟩) (by norm_num)
  have hy₁ := transSolve_spec hq1 (stepXPS X₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁
      r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w))
  have hy₂ := transSolve_spec hq2 (stepXPS X₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂
      r)) 1 w) -
          stepFieldS ha hp hpb T₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w))
  have := stepPullback_bounds ha hp hpb hσ hσ1 hσs hη0 hη hF₁ hF₂ hM0 hMs hN₁ hZZ hY0
    hY₁ hY₂ hb₁ hb₂ hd hw (t := 1) ⟨by norm_num, le_rfl⟩ hy₁ hy₂
  exact this

/-- Per-time bounds for the commutator term (two parameters). -/
theorem stepXplusB_time_bounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {T₁ T₂ : HomTaylor_gen a p pb s} {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)} {Δ₁ N₁ : ℝ}
    (he₁ : 0 ≤ e₁) (hΔ₁ : 0 ≤ Δ₁) (hN₁ : 0 ≤ N₁)
    (hT₁ : HomFieldBound_gen ha hp hpb r e₁ T₁) (hT₂ : HomFieldBound_gen ha hp hpb r e₁ T₂)
    (hTn₁ : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T₁))
    (hTn₂ : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T₂))
    (hΔT : HomFieldBound_gen ha hp hpb r Δ₁ (T₁.homSub T₂))
    (hΔTn : HomFieldBound_gen ha hp hpb r (2 * Δ₁)
      ((homNhatTaylor_gen T₁).homSub (homNhatTaylor_gen T₂)))
    (hF₁ : HomFieldBound_gen ha hp hpb r Mf FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r Mf FT₂)
    (hΔF : HomFieldBound_gen ha hp hpb r N₁ (FT₁.homSub FT₂))
    (hM0 : 0 < Mf) (hMs : 16 * Mf ≤ σ * η ^ 2)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let ι := stepEmbedCLM a p pb hpb r
    stepNu (η * r) (yfam ι (stepFieldS ha hp hpb FT₁ r) (stepZgfam ha hp hpb T₁ FT₁) t w) ≤
        2 * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) ∧
      stepNu (η * r) (yfam ι (stepFieldS ha hp hpb FT₁ r) (stepZgfam ha hp hpb T₁ FT₁) t w -
          yfam ι (stepFieldS ha hp hpb FT₂ r) (stepZgfam ha hp hpb T₂ FT₂) t w) ≤
        2 * (η⁻¹ ^ 2 * (8 * (Mf * Δ₁ + e₁ * N₁) / σ) +
          2 * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) := by
  intro ι
  have hr : 0 < r := Fact.out
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  have hMσ : Mf ≤ σ / 1024 := by nlinarith
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hdomU : ∀ x : KamPhase, x ∈ kamDomain (s - 3 * σ) (4 * (η * r)) →
      StepPhase.ofK (r := r) x ∈ stepDomain r (s - 2 * σ) (r / 2) := fun x hx =>
    stepDomain_mono' (ρ := r) (by linarith) (by positivity) (by nlinarith) hx
  have hq1 : ‖transNop ι (stepFieldS ha hp hpb FT₁ r) t w‖ < 1 :=
    lt_of_le_of_lt (stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF₁ hM0 hMσ
      (hU'sub hw) ⟨by linarith [ht.1], ht.2⟩) (by norm_num)
  have hq2 : ‖transNop ι (stepFieldS ha hp hpb FT₂ r) t w‖ < 1 :=
    lt_of_le_of_lt (stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF₂ hM0 hMσ
      (hU'sub hw) ⟨by linarith [ht.1], ht.2⟩) (by norm_num)
  have hy₁ := transSolve_spec hq1 (stepZgfam ha hp hpb T₁ FT₁ t (holoFlow (smoothField ι
    (stepFieldS ha hp hpb FT₁ r)) t w))
  have hy₂ := transSolve_spec hq2 (stepZgfam ha hp hpb T₂ FT₂ t (holoFlow (smoothField ι
    (stepFieldS ha hp hpb FT₂ r)) t w))
  have hY0 : 0 ≤ η⁻¹ ^ 2 * (8 * e₁ * Mf / σ) := by positivity
  have hnorm : ∀ (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
      (hT : HomFieldBound_gen ha hp hpb r e₁ T)
      (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
      (hF : HomFieldBound_gen ha hp hpb r Mf FT) (x : KamPhase),
      x ∈ kamDomain (s - 3 * σ) (4 * (η * r)) →
      kamNorm (η * r) (StepPhase.toK (stepZgfam ha hp hpb T FT t (StepPhase.ofK (r := r) x))) ≤
        η⁻¹ ^ 2 * (8 * e₁ * Mf / σ) := by
    intro T FT hT hTn hF x hx
    have h1 := norm_stepZgfam_le (σ := σ) hσ hσ1 (by linarith : 2 * σ < s) he₁ hM0.le hT hTn hF ht
      (hdomU x hx)
    have h2 := (stepNu_mono (y := stepZgfam ha hp hpb T FT t (StepPhase.ofK (r := r) x)) hη0
      (by linarith)).2
    exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  have hholo : ∀ (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
      (hT : HomFieldBound_gen ha hp hpb r e₁ T)
      (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
      (hF : HomFieldBound_gen ha hp hpb r Mf FT),
      DifferentiableOn ℂ (fun x : KamPhase =>
        StepPhase.toK (stepZgfam ha hp hpb T FT t (StepPhase.ofK (r := r) x)))
        (kamDomain (s - 3 * σ) (4 * (η * r))) := by
    intro T FT hT hTn hF
    exact (stepToKCLM r).differentiable.comp_differentiableOn
      ((stepZgfam_differentiableOn hσ hσ1 (by linarith : 2 * σ < s) he₁ hM0.le hT hTn hF t).comp
        (stepOfKCLM r).differentiable.differentiableOn hdomU)
  have hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS ha hp hpb FT₁ r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N₁ := by
    intro z hz
    rw [← stepFieldS_sub ha hp hpb FT₁ FT₂ (stepDomain_theta_mem le_rfl hz)]
    exact stepFieldS_bound ha hp hpb _ r hΔF le_rfl hz
  have hd : ∀ x ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (StepPhase.toK (stepZgfam ha hp hpb T₁ FT₁ t (StepPhase.ofK (r := r) x)) -
        StepPhase.toK (stepZgfam ha hp hpb T₂ FT₂ t (StepPhase.ofK (r := r) x))) ≤
        η⁻¹ ^ 2 * (8 * (Mf * Δ₁ + e₁ * N₁) / σ) := by
    intro x hx
    have hz := hdomU x hx
    have bN := stepBrZ_sub_norm_le (TG := homNhatTaylor_gen T₁) (FT := FT₁)
      (TG₂ := homNhatTaylor_gen T₂) (FT₂ := FT₂) (σ := σ) ha hp hpb hσ hσ1
      (by linarith : 2 * σ < s) (by linarith) (by linarith) hM0.le hN₁ hTn₂ hF₂ hTn₁ hΔTn hF₁ hΔF hz
    have bR := stepBrZ_sub_norm_le (TG := T₁) (FT := FT₁) (TG₂ := T₂) (FT₂ := FT₂) (σ := σ) ha hp
      hpb hσ hσ1 (by linarith : 2 * σ < s) he₁ hΔ₁ hM0.le hN₁ hT₂ hF₂ hT₁ hΔT hF₁ hΔF hz
    have e : stepZgfam ha hp hpb T₁ FT₁ t (StepPhase.ofK (r := r) x) -
        stepZgfam ha hp hpb T₂ FT₂ t (StepPhase.ofK (r := r) x) =
        (1 - (t : ℂ)) • (stepBrZ ha hp hpb (homNhatTaylor_gen T₁) FT₁ (StepPhase.ofK (r := r) x) -
          stepBrZ ha hp hpb (homNhatTaylor_gen T₂) FT₂ (StepPhase.ofK (r := r) x)) +
        (t : ℂ) • (stepBrZ ha hp hpb T₁ FT₁ (StepPhase.ofK (r := r) x) -
          stepBrZ ha hp hpb T₂ FT₂ (StepPhase.ofK (r := r) x)) := by
      unfold stepZgfam; module
    have hb : ‖stepZgfam ha hp hpb T₁ FT₁ t (StepPhase.ofK (r := r) x) -
        stepZgfam ha hp hpb T₂ FT₂ t (StepPhase.ofK (r := r) x)‖ ≤ 8 * (Mf * Δ₁ + e₁ * N₁) / σ := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
      have a1 : ‖(1 - (t : ℂ))‖ = 1 - t := by
        rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      have a2 : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      rw [a1, a2]
      have bN' : ‖stepBrZ ha hp hpb (homNhatTaylor_gen T₁) FT₁ (StepPhase.ofK (r := r) x) -
          stepBrZ ha hp hpb (homNhatTaylor_gen T₂) FT₂ (StepPhase.ofK (r := r) x)‖ ≤
          8 * (Mf * Δ₁ + e₁ * N₁) / σ := bN.trans (le_of_eq (by ring))
      have bR' : ‖stepBrZ ha hp hpb T₁ FT₁ (StepPhase.ofK (r := r) x) -
          stepBrZ ha hp hpb T₂ FT₂ (StepPhase.ofK (r := r) x)‖ ≤
          8 * (Mf * Δ₁ + e₁ * N₁) / σ := by
        refine bR.trans ?_
        have : 0 ≤ (Mf * Δ₁ + e₁ * N₁) / σ := by positivity
        have e2 : 4 * (Mf * Δ₁ + e₁ * N₁) / σ = 4 * ((Mf * Δ₁ + e₁ * N₁) / σ) := by ring
        have e3 : 8 * (Mf * Δ₁ + e₁ * N₁) / σ = 8 * ((Mf * Δ₁ + e₁ * N₁) / σ) := by ring
        rw [e2, e3]; linarith
      nlinarith [ht.1, ht.2, norm_nonneg (stepBrZ ha hp hpb (homNhatTaylor_gen T₁) FT₁
          (StepPhase.ofK (r := r) x) -
          stepBrZ ha hp hpb (homNhatTaylor_gen T₂) FT₂ (StepPhase.ofK (r := r) x)),
        norm_nonneg (stepBrZ ha hp hpb T₁ FT₁ (StepPhase.ofK (r := r) x) -
          stepBrZ ha hp hpb T₂ FT₂ (StepPhase.ofK (r := r) x))]
    have h2 := (stepNu_mono (y := stepZgfam ha hp hpb T₁ FT₁ t (StepPhase.ofK (r := r) x) -
      stepZgfam ha hp hpb T₂ FT₂ t (StepPhase.ofK (r := r) x)) hη0 (by linarith)).2
    exact h2.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hpb' := stepPullback_bounds ha hp hpb hσ hσ1 hσs hη0 hη hF₁ hF₂ hM0 hMs hN₁ hZZ hY0
    (hholo T₁ FT₁ hT₁ hTn₁ hF₁) (hholo T₂ FT₂ hT₂ hTn₂ hF₂)
    (fun x hx => hnorm T₁ FT₁ hT₁ hTn₁ hF₁ x hx) (fun x hx => hnorm T₂ FT₂ hT₂ hTn₂ hF₂ x hx)
    hd hw (t := t) ⟨by linarith [ht.1], ht.2⟩ hy₁ hy₂
  exact hpb'

/-- `t ↦ y_t(w)` is Lipschitz (in the norm of `StepPhase r`). -/
theorem stepYfam_time_lip (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8) {T : HomTaylor_gen a p pb s}
    {FT : HomTaylor_gen a p pb (s - σ)} (he₁ : 0 ≤ e₁)
    (hT : HomFieldBound_gen ha hp hpb r e₁ T)
    (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hM0 : 0 < Mf) (hMσ : Mf ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
      ‖yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) (stepZgfam ha hp hpb T FT) t w -
        yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) (stepZgfam ha hp hpb T FT) t'
            w‖
          ≤ L * |t - t'| := by
  have hr : 0 < r := Fact.out
  have hMδ : Mf < σ / 4 := by linarith
  have ctx := StepCtx.mk' ha hp hpb hσ hσ1 (by linarith : 2 * σ < s) hF hM0 hMδ
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hι : ∀ g, ‖stepEmbedCLM a p pb hpb r g‖ ≤ ‖g‖ := norm_stepEmbedCLM_apply_le a p pb hpb r
  have hL : 0 ≤ Mf / (σ / 4) := by positivity
  have hball : ∀ z ∈ ball w (σ / 16), ball z (σ / 16) ⊆ stepDomain r (s - 2 * σ) (r / 2) := by
    intro z hz y hy
    have hm := stepDomain_U_margin hσ hσ1 (by linarith : 3 * σ < s) (hU'sub hw)
    refine hm ?_
    rw [mem_ball] at hz hy ⊢
    have := dist_triangle y z w
    linarith
  have hN : ∀ t ∈ Icc (0 : ℝ) 1, ‖transNop (stepEmbedCLM a p pb hpb r)
      (stepFieldS ha hp hpb FT r) t w‖ ≤ 1 / 128 := fun t ht =>
    stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF hM0 hMσ (hU'sub hw)
      ⟨by linarith [ht.1], ht.2⟩
  have hY0 : 0 ≤ 8 * e₁ * Mf / σ := by positivity
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (stepZgfam ha hp hpb T FT t)
      (stepDomain r (s - 2 * σ) (r / 2)) := fun t ht =>
    stepZgfam_differentiableOn hσ hσ1 (by linarith : 2 * σ < s) he₁ hM0.le hT hTn hF t
  have hnb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ stepDomain r (s - 2 * σ) (r / 2),
      ‖stepZgfam ha hp hpb T FT t z‖ ≤ 8 * e₁ * Mf / σ := fun t ht z hz =>
    norm_stepZgfam_le hσ hσ1 (by linarith : 2 * σ < s) he₁ hM0.le hT hTn hF ht hz
  have hnt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ∀ z ∈ stepDomain r (s - 2 * σ) (r / 2),
      ‖stepZgfam ha hp hpb T FT t z - stepZgfam ha hp hpb T FT t' z‖ ≤ 12 * e₁ * Mf / σ * |t - t'|
          :=
    fun t ht t' ht' z hz => norm_stepZgfam_sub_le hσ hσ1 (by linarith : 2 * σ < s) he₁ hM0.le
      hT hTn hF hz
  refine ⟨((8 * e₁ * Mf / σ) / (σ / 16) * Mf + 12 * e₁ * Mf / σ +
    Mf / (σ / 4) * Real.exp (Mf / (σ / 4)) * ((8 * e₁ * Mf / σ) / (1 - 1 / 128))) / (1 - 1 / 128),
    by positivity, fun t ht t' ht' => ?_⟩
  exact norm_yfam_time_sub_le ctx.flow ctx.holo ctx.bound hι hL (stepDomain_isOpen _ _ _)
    (by positivity : 0 < σ / 16) (by linarith) (by norm_num) hY0 (by positivity) hdiff hnb hnt
    (hU'U hw) (hball) hN ht ht'

/-- **The commutator integral** `∫₀¹ y_t dt`: sup bound and two-parameter difference bound. -/
theorem stepXplusB_bounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {T₁ T₂ : HomTaylor_gen a p pb s} {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)} {Δ₁ N₁ : ℝ}
    (he₁ : 0 ≤ e₁) (hΔ₁ : 0 ≤ Δ₁) (hN₁ : 0 ≤ N₁)
    (hT₁ : HomFieldBound_gen ha hp hpb r e₁ T₁) (hT₂ : HomFieldBound_gen ha hp hpb r e₁ T₂)
    (hTn₁ : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T₁))
    (hTn₂ : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T₂))
    (hΔT : HomFieldBound_gen ha hp hpb r Δ₁ (T₁.homSub T₂))
    (hΔTn : HomFieldBound_gen ha hp hpb r (2 * Δ₁)
      ((homNhatTaylor_gen T₁).homSub (homNhatTaylor_gen T₂)))
    (hF₁ : HomFieldBound_gen ha hp hpb r Mf FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r Mf FT₂)
    (hΔF : HomFieldBound_gen ha hp hpb r N₁ (FT₁.homSub FT₂))
    (hM0 : 0 < Mf) (hMs : 16 * Mf ≤ σ * η ^ 2)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    let ι := stepEmbedCLM a p pb hpb r
    stepNu (η * r) (∫ t in (0 : ℝ)..1,
        yfam ι (stepFieldS ha hp hpb FT₁ r) (stepZgfam ha hp hpb T₁ FT₁) t w) ≤
        2 * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) ∧
      stepNu (η * r) ((∫ t in (0 : ℝ)..1,
          yfam ι (stepFieldS ha hp hpb FT₁ r) (stepZgfam ha hp hpb T₁ FT₁) t w) -
        ∫ t in (0 : ℝ)..1, yfam ι (stepFieldS ha hp hpb FT₂ r) (stepZgfam ha hp hpb T₂ FT₂) t w) ≤
        2 * (η⁻¹ ^ 2 * (8 * (Mf * Δ₁ + e₁ * N₁) / σ) +
          2 * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) := by
  intro ι
  have hr : 0 < r := Fact.out
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  have hMσ : Mf ≤ σ / 1024 := by nlinarith
  have hρ : 0 < η * r := by positivity
  obtain ⟨L₁, hL₁, hl₁⟩ := stepYfam_time_lip ha hp hpb hσ hσ1 hσs hη0 hη he₁ hT₁ hTn₁ hF₁ hM0 hMσ hw
  obtain ⟨L₂, hL₂, hl₂⟩ := stepYfam_time_lip ha hp hpb hσ hσ1 hσs hη0 hη he₁ hT₂ hTn₂ hF₂ hM0 hMσ hw
  have hb := fun t ht => stepXplusB_time_bounds ha hp hpb hσ hσ1 hσs hη0 hη he₁ hΔ₁ hN₁ hT₁ hT₂
    hTn₁ hTn₂ hΔT hΔTn hF₁ hF₂ hΔF hM0 hMs hw (t := t) ht
  refine ⟨?_, ?_⟩
  · have := stepNu_integral_sub_le hρ (f₁ := fun t => yfam ι (stepFieldS ha hp hpb FT₁ r)
      (stepZgfam ha hp hpb T₁ FT₁) t w) (f₂ := fun _ => 0) (L₁ := L₁) (L₂ := 0) (K := 2 * (η⁻¹ ^ 2
          * (8 * e₁ * Mf / σ)))
      hL₁ le_rfl hl₁ (fun _ _ _ _ => by simp) (fun t ht => by
        simpa using (hb t ht).1)
    simpa using this
  · exact stepNu_integral_sub_le hρ (f₁ := fun t => yfam ι (stepFieldS ha hp hpb FT₁ r)
      (stepZgfam ha hp hpb T₁ FT₁) t w) (f₂ := fun t => yfam ι (stepFieldS ha hp hpb FT₂ r)
      (stepZgfam ha hp hpb T₂ FT₂) t w) hL₁ hL₂ hl₁ hl₂ (fun t ht => (hb t ht).2)

/-- **Bounds of `X_+`** for two parameters: sum of the pulled-back and commutator terms. -/
theorem stepXplus_pair_bound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {X₁ X₂ : KamPhase → KamPhase} {T₁ T₂ : HomTaylor_gen a p pb s}
    {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)} {Δ₁ N₁ Y0 Yd : ℝ}
    (he₁ : 0 ≤ e₁) (hΔ₁ : 0 ≤ Δ₁) (hN₁ : 0 ≤ N₁) (hY0 : 0 ≤ Y0)
    (hT₁ : HomFieldBound_gen ha hp hpb r e₁ T₁) (hT₂ : HomFieldBound_gen ha hp hpb r e₁ T₂)
    (hTn₁ : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T₁))
    (hTn₂ : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T₂))
    (hΔT : HomFieldBound_gen ha hp hpb r Δ₁ (T₁.homSub T₂))
    (hΔTn : HomFieldBound_gen ha hp hpb r (2 * Δ₁)
      ((homNhatTaylor_gen T₁).homSub (homNhatTaylor_gen T₂)))
    (hF₁ : HomFieldBound_gen ha hp hpb r Mf FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r Mf FT₂)
    (hΔF : HomFieldBound_gen ha hp hpb r N₁ (FT₁.homSub FT₂))
    (hM0 : 0 < Mf) (hMs : 16 * Mf ≤ σ * η ^ 2)
    (hY₁ : DifferentiableOn ℂ (fun x => X₁ x - stepField ha hp hpb T₁ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hY₂ : DifferentiableOn ℂ (fun x => X₂ x - stepField ha hp hpb T₂ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hb₁ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₁ z - stepField ha hp hpb T₁ z) ≤ Y0)
    (hb₂ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₂ z - stepField ha hp hpb T₂ z) ≤ Y0)
    (hd : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) ((X₁ z - stepField ha hp hpb T₁ z) - (X₂ z - stepField ha hp hpb T₂ z)) ≤ Yd)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    stepNu (η * r) (stepXplusS ha hp hpb X₁ T₁ FT₁ w) ≤
        2 * Y0 + 2 * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) ∧
      stepNu (η * r) (stepXplusS ha hp hpb X₁ T₁ FT₁ w - stepXplusS ha hp hpb X₂ T₂ FT₂ w) ≤
        (2 * (Yd + 2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
          4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * Y0) +
        (2 * (η⁻¹ ^ 2 * (8 * (Mf * Δ₁ + e₁ * N₁) / σ) +
          2 * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ)) / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * (η⁻¹ ^ 2 * (8 * e₁ * Mf / σ))) := by
  have hρ : 0 < η * r := by have : 0 < r := Fact.out; positivity
  obtain ⟨A1, A2⟩ := stepXplusA_bounds ha hp hpb hσ hσ1 hσs hη0 hη hF₁ hF₂ hM0 hMs hN₁
    (fun z hz => by
      rw [← stepFieldS_sub ha hp hpb FT₁ FT₂ (stepDomain_theta_mem le_rfl hz)]
      exact stepFieldS_bound ha hp hpb _ r hΔF le_rfl hz) hY0 hY₁ hY₂ hb₁ hb₂ hd hw
  obtain ⟨B1, B2⟩ := stepXplusB_bounds ha hp hpb hσ hσ1 hσs hη0 hη he₁ hΔ₁ hN₁ hT₁ hT₂ hTn₁
    hTn₂ hΔT hΔTn hF₁ hF₂ hΔF hM0 hMs hw
  unfold stepXplusS
  refine ⟨(stepNu_add hρ _ _).trans (add_le_add A1 B1), ?_⟩
  have e : transSolve (transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) 1 w)
        (stepXPS X₁ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
            (stepFieldS ha hp hpb FT₁ r)) 1 w)) +
      (∫ t in (0 : ℝ)..1, yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r)
        (stepZgfam ha hp hpb T₁ FT₁) t w) -
      (transSolve (transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r) 1 w)
        (stepXPS X₂ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₂ r)) 1 w) -
          stepFieldS ha hp hpb T₂ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
            (stepFieldS ha hp hpb FT₂ r)) 1 w)) +
      (∫ t in (0 : ℝ)..1, yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r)
        (stepZgfam ha hp hpb T₂ FT₂) t w)) =
      (transSolve (transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r) 1 w)
        (stepXPS X₁ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
            (stepFieldS ha hp hpb FT₁ r)) 1 w)) -
      transSolve (transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r) 1 w)
        (stepXPS X₂ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT₂ r)) 1 w) -
          stepFieldS ha hp hpb T₂ r (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
            (stepFieldS ha hp hpb FT₂ r)) 1 w))) +
      ((∫ t in (0 : ℝ)..1, yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₁ r)
        (stepZgfam ha hp hpb T₁ FT₁) t w) -
       ∫ t in (0 : ℝ)..1, yfam (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT₂ r)
        (stepZgfam ha hp hpb T₂ FT₂) t w) := by abel
  rw [e]
  exact (stepNu_add hρ _ _).trans (add_le_add A2 B2)

end KAM.Wave