/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.EnvelopeIntegrals
public import KAM.Nekhoroshev.Averaging.Exit
public import KAM.Nekhoroshev.Averaging.Pointwise
public import KAM.Nekhoroshev.Averaging.Transport

/-!
# Part N12: the stopped maximum majorant (`bpN:p12:s-trans#psi`, `bpN:p12:stopped`)

`avgStopped` is the pointwise majorant of the displacement up to the stopping time: the corrector
term plus `ε` times the envelope integrated along the orbit, with the integrand killed outside the
stay set. `stopped` fixes `M₂` and `A₁` before `ε` and before any size-one perturbation `f₁`, and
proves that on a compact `K` the killed integrand is Borel (`st-meas`), the majorant bounds the
displacement at every time up to the stop (`st-pt`, from `pointwise` and `exit`) and its integral
over `K` is at most `A₁ √ε` (`st-int`): `K` is covered by finitely many half-open angle cells, on
each cell `transport` (also at time zero) converts the integral along the flow into the integral
of the envelope over `avgG n R`, and the time interval has length `1/ε`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

def avgStopped (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R s M₂ ε : ℝ) (x : AvgPhase n) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * ε) * avgWenv h s (Real.sqrt ε) x.2 + ENNReal.ofReal ε *
    ∫⁻ t in Icc 0 (1 / ε), (avgStay h f R ε).indicator
      (fun p => avgPhiEnv h s M₂ ε (Real.sqrt ε) (avgFlow h f R ε p.1 p.2).2) (t, x)

section Measurability

variable (d : AveragingData n R s h f) (ε : ℝ)
include d

/-- The stay set is Borel: it is relatively open in `[0,∞) × {y | y.2 ∈ B(0,R/2)}`. -/
theorem measurableSet_avgStay : MeasurableSet (avgStay h f R ε) := by
  have hO := isOpen_avgStay_relative d ε
  set c : Set.Ici (0 : ℝ) × {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)} →
      ℝ × AvgPhase n := fun p => (((p.1 : ℝ), (p.2 : AvgPhase n)) : ℝ × AvgPhase n) with hcdef
  have hc : Topology.IsInducing c :=
    Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal
  obtain ⟨U, hU, hUe⟩ := hc.isOpen_iff.1 hO
  have hS : MeasurableSet ((Ici (0 : ℝ)) ×ˢ {y : AvgPhase n | y.2 ∈ actionBall n (R / 2)}) :=
    measurableSet_Ici.prod (measurableSet_ball.preimage measurable_snd)
  suffices hEq : avgStay h f R ε =
      U ∩ ((Ici (0 : ℝ)) ×ˢ {y : AvgPhase n | y.2 ∈ actionBall n (R / 2)}) from
    hEq ▸ hU.measurableSet.inter hS
  ext p
  constructor
  · intro hp
    have h1 : (⟨⟨p.1, hp.1⟩, ⟨p.2, hp.2.1⟩⟩ : Set.Ici (0 : ℝ) ×
        {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)}) ∈ c ⁻¹' U := by
      rw [hUe]; exact hp
    exact ⟨h1, hp.1, hp.2.1⟩
  · rintro ⟨hpU, h0, h2⟩
    have : (⟨⟨p.1, h0⟩, ⟨p.2, h2⟩⟩ : Set.Ici (0 : ℝ) ×
        {y : AvgPhase n // y.2 ∈ actionBall n (R / 2)}) ∈ c ⁻¹' U := hpU
    rw [hUe] at this
    exact this

/-- `st-meas`: the killed integrand is jointly Borel. -/
theorem measurable_killed {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable ((avgStay h f R ε).indicator
      (fun p => Φ (avgFlow h f R ε p.1 p.2).2)) := by
  have hΩ : MeasurableSet (avgFlowDomain h f R ε) := (isOpen_avgFlowDomain d ε).measurableSet
  have hsub : avgStay h f R ε ⊆ avgFlowDomain h f R ε := fun p hp => hp.2.2.1
  refine measurable_of_restrict_of_restrict_compl hΩ ?_ ?_
  · have hcont : Continuous fun q : avgFlowDomain h f R ε => avgFlow h f R ε q.1.1 q.1.2 :=
      (continuousOn_avgFlow d ε).comp_continuous continuous_subtype_val fun q => q.2
    have hG : Measurable fun q : avgFlowDomain h f R ε =>
        Φ (avgFlow h f R ε q.1.1 q.1.2).2 := hΦ.comp (continuous_snd.comp hcont).measurable
    refine Measurable.ite ?_ hG measurable_const
    exact measurable_subtype_coe (measurableSet_avgStay d ε)
  · have : (avgFlowDomain h f R ε)ᶜ.domRestrict ((avgStay h f R ε).indicator
        (fun p => Φ (avgFlow h f R ε p.1 p.2).2)) = fun _ => (0 : ℝ≥0∞) := by
      funext q
      exact indicator_of_notMem (fun hq => q.2 (hsub hq)) _
    rw [this]; exact measurable_const

end Measurability

end KAM.Nekhoroshev

end
