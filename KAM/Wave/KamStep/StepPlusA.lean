/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusFinal
public import KAM.Wave.KamStep.Class
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The pulled-back term `(P - R) ∘ Φ` (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepSympCLM_embed_apply`: `ϖ_{p,p}(ι g, W) = ϖ_{p_+,p}(g, W)`. The function `Q₀ = P - R` on
`StepPhase r` has derivative `B(ι(X_P - X_R), ·)` on `D(s,r)`; its pull-back by the flow is a
smoothing Hamiltonian with field `(1 + N_1)⁻¹ (X_P - X_R)(Φ w)`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf e₁ : ℝ} [Fact (0 < r)]

theorem stepSympCLM_embed_apply (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (g W : StepPhase r) :
    stepSympCLM (q := p) (q' := p) ha (by linarith) r (stepEmbedCLM a p pb hpb r g) W =
      stepSymp (q := pb) (q' := p) ha (by linarith) (StepPhase.toK g) (StepPhase.toK W) := by
  rw [stepSympCLM_apply, stepEmbedCLM_apply, stepSymp_embed ha hpb (by linarith)
    (by linarith : 0 ≤ p + pb), stepSymp_comm_weights ha (by linarith) (by linarith)]

/-- `P` as a function on `StepPhase r`. -/
def stepPS (P : KamPhase → ℂ) (r : ℝ) : StepPhase r → ℂ := fun z => P (StepPhase.toK z)

/-- The field of `P` as a map into `StepPhase r`. -/
def stepXPS (X : KamPhase → KamPhase) (r : ℝ) : StepPhase r → StepPhase r :=
  fun z => StepPhase.ofK (X (StepPhase.toK z))

theorem stepPS_hasFDerivAt (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {s : ℝ}
    {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    {z : StepPhase r} (hz : StepPhase.toK z ∈ kamDomain s r) :
    HasFDerivAt (stepPS P r)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (stepEmbedCLM a p pb hpb r (stepXPS X r z))) z := by
  have hd : DifferentiableAt ℂ P (StepPhase.toK z) :=
    hP.holoP.differentiableAt ((kamDomain_isOpen s r).mem_nhds hz)
  have h : HasFDerivAt (stepPS P r) ((fderiv ℂ P (StepPhase.toK z)).comp (stepToKCLM r)) z :=
    hd.hasFDerivAt.comp z (stepToKCLM r).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  rw [stepSympCLM_embed_apply ha hp hpb]
  simp only [ContinuousLinearMap.comp_apply, stepToKCLM_apply]
  rw [hP.deriv_eq _ hz]
  rfl

theorem stepPlusA_smoothing (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024) :
    let ι := stepEmbedCLM a p pb hpb r
    let Z := stepFieldS ha hp hpb FT r
    let B := stepSympCLM (q := p) (q' := p) ha (by linarith) r
    let Q0 : StepPhase r → ℂ := fun z => stepPS P r z - stepFS ha hp hpb T r z
    let Z0 : StepPhase r → StepPhase r := fun z => stepXPS X r z - stepFieldS ha hp hpb T r z
    (∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      HasFDerivAt (fun w => Q0 (holoFlow (smoothField ι Z) 1 w))
        (B (ι (transSolve (transNop ι Z 1 w) (Z0 (holoFlow (smoothField ι Z) 1 w))))) w) ∧
    DifferentiableOn ℂ
      (fun w => transSolve (transNop ι Z 1 w) (Z0 (holoFlow (smoothField ι Z) 1 w)))
      (stepDomain r (s - 5 * σ) (η * r)) := by
  intro ι Z B Q0 Z0
  have hr : 0 < r := Fact.out
  have hMδ : Mf < σ / 4 := by linarith
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hVd : ∀ z ∈ stepDomain r (s - σ) r,
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ : DifferentiableOn ℂ Z (stepDomain r (s - σ) r) :=
    (stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVd
  have hb : ∀ z ∈ stepDomain r (s - σ) r, ‖Z z‖ ≤ Mf := fun z hz =>
    stepFieldS_bound ha hp hpb FT r hF le_rfl hz
  have hι : ∀ g, ‖ι g‖ ≤ ‖g‖ := norm_stepEmbedCLM_apply_le a p pb hpb r
  have hskew : ∀ z ∈ stepDomain r (s - σ) r, ∀ x y,
      B (fderiv ℂ (smoothField ι Z) z x) y + B x (fderiv ℂ (smoothField ι Z) z y) = 0 :=
    fun z hz x y => stepFieldS_skew ha hp hpb FT r (stepDomain_theta_mem le_rfl hz) x y
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hN : ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ‖transNop ι Z 1 w‖ ≤ 1 / 128 := fun w hw =>
    stepN_bound ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hFlow hZ hb hMf (hU'sub hw)
      ⟨by norm_num, le_rfl⟩
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hφV : ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      holoFlow (smoothField ι Z) 1 w ∈ stepDomain r (s - σ) r := fun w hw =>
    hFlow.mem_V_of_ball (hU'U hw) (holoFlow_mem_ball hFlow (hU'U hw) h1)
  have hφD : ∀ w ∈ stepDomain r (s - σ) r, StepPhase.toK w ∈ kamDomain s r := fun w hw =>
    kamDomain_mono (by linarith) hr le_rfl hw
  have hQ0 : ∀ z ∈ stepDomain r (s - σ) r, HasFDerivAt Q0 (B (ι (Z0 z))) z := by
    intro z hz
    have h2 := stepPS_hasFDerivAt ha hp hpb hP (hφD z hz)
    have h3 := stepFS_hasFDerivAt ha hp hpb T r (W := z)
      (by have := hφD z hz; exact fun i => this.1 i)
    have h4 : HasFDerivAt Q0 _ z := h2.sub h3
    refine h4.congr_fderiv ?_
    simp only [Z0, map_sub]
    rfl
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · refine hasFDerivAt_comp_flow_smooth hFlow hZ hb B hskew (hU'U hw) h1 (Gf := Q0) (Zg := Z0)
      (hQ0 _ (hφV w hw)) ?_
    exact transSolve_spec (lt_of_le_of_lt (hN w hw) (by norm_num)) _
  · have hwU := hU'U hw
    have hNd : DifferentiableAt ℂ (fun w => transNop ι Z 1 w) w :=
      (differentiableOn_transNop hFlow hZ hb h1).differentiableAt (hFlow.isOpen_U.mem_nhds hwU)
    have hφd : DifferentiableAt ℂ (holoFlow (smoothField ι Z) 1) w :=
      (holomorphicOn_holoFlow hFlow h1).differentiableAt (hFlow.isOpen_U.mem_nhds hwU)
    have hz := hφV w hw
    have hXd : DifferentiableAt ℂ (stepXPS X r) (holoFlow (smoothField ι Z) 1 w) := by
      have hd := hP.holoX.differentiableAt ((kamDomain_isOpen s r).mem_nhds (hφD _ hz))
      exact (stepOfKCLM r).differentiableAt.comp _ (hd.comp _ (stepToKCLM r).differentiableAt)
    have hRd : DifferentiableAt ℂ (stepFieldS ha hp hpb T r) (holoFlow (smoothField ι Z) 1 w) :=
      stepFieldS_differentiableAt ha hp hpb T r (stepDomain_theta_mem (by linarith) hz)
    exact (differentiableAt_transSolve_apply hNd ((hXd.sub hRd).comp w hφd)
      (lt_of_le_of_lt (hN w hw) (by norm_num))).differentiableWithinAt

end KAM.Wave
