/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Phase
public import KAM.Wave.Analytic.Flow.Holomorphic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The flow with explicit margins (`bpW:w5:flow`, steps `f-margin`, `f-flow`)

On `StepPhase r` (the carrier of `bpW:w1:flow`) put `V = D(s-σ, r)`, `U = D(s-2σ, r/2)` and
`δ = σ/4`. Then `V`, `U` are open, and for a field `X` holomorphic on `V` with `|X| ≤ M < σ/4`
the hypotheses of the landed flow lemma hold (`stepFlowHyp`); all flow lemmas of
`KAM/Wave/Analytic/Flow` apply with these margins. The numerical form `M ≤ σ/256` is
`stepMF_margins` (`KamStep/Data`).
-/

@[expose] public section

namespace KAM.Wave

open Metric

/-- The additive identification `StepPhase r → KamPhase`. -/
def StepPhase.toKHom (r : ℝ) : StepPhase r →+ KamPhase where
  toFun := StepPhase.toK
  map_zero' := rfl
  map_add' _ _ := rfl

theorem stepPhase_toK_continuous (r : ℝ) [Fact (0 < r)] :
    Continuous (StepPhase.toK : StepPhase r → KamPhase) := by
  have hr : 0 < r := Fact.out
  exact AddMonoidHomClass.continuous_of_bound (StepPhase.toKHom r) (max 1 (max (r ^ 2) r))
    fun W => norm_kamPhase_le_kamNorm hr (StepPhase.toK W)

/-- `D(s, r')` as a subset of `StepPhase ρ` (the carrier norm is `|·|_ρ`). -/
def stepDomain (ρ s r' : ℝ) : Set (StepPhase ρ) := {W | StepPhase.toK W ∈ kamDomain s r'}

theorem stepDomain_isOpen (ρ s r' : ℝ) [Fact (0 < ρ)] : IsOpen (stepDomain ρ s r') :=
  (kamDomain_isOpen s r').preimage (stepPhase_toK_continuous ρ)

/-- **Margins** (`bpW:w5:flow`, step `f-margin`): every `w ∈ D(s-2σ, r/2)` has
`B(w, 2δ) = B(w, σ/2) ⊆ D(s-σ, r)`. -/
theorem stepDomain_margin {s σ r : ℝ} [Fact (0 < r)] (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσs : 2 * σ < s)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ball w (2 * (σ / 4)) ⊆ stepDomain r (s - σ) r := by
  have hr : 0 < r := Fact.out
  intro z hz
  rw [mem_ball, dist_eq_norm, stepPhase_norm_eq] at hz
  have hz' : kamNorm r (StepPhase.toK z - StepPhase.toK w) < σ / 2 := by
    have : 2 * (σ / 4) = σ / 2 := by ring
    rw [this] at hz; exact hz
  have h : StepPhase.toK w + (StepPhase.toK z - StepPhase.toK w) ∈ kamDomain (s - σ) r :=
    kamDomain_add_mem hσ hσ1 hσs hr hw hz'
  have e : StepPhase.toK w + (StepPhase.toK z - StepPhase.toK w) = StepPhase.toK z := by
    rw [add_sub_cancel]
  rw [e] at h
  exact h

/-- **The flow hypotheses with the concrete margins** (`bpW:w5:flow`): for `X` holomorphic on
`V = D(s-σ, r)` with `|X| ≤ M`, `0 < M < σ/4`, `FlowHyp X V U M (σ/4)` holds with
`U = D(s-2σ, r/2)`. -/
theorem stepFlowHyp {s σ r M : ℝ} [Fact (0 < r)] (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσs : 2 * σ < s)
    {X : StepPhase r → StepPhase r} (hX : DifferentiableOn ℂ X (stepDomain r (s - σ) r))
    (hb : ∀ z ∈ stepDomain r (s - σ) r, ‖X z‖ ≤ M) (hM : 0 < M) (hMδ : M < σ / 4) :
    FlowHyp X (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) M (σ / 4) := by
  refine ⟨stepDomain_isOpen _ _ _, stepDomain_isOpen _ _ _, hX, hb, ?_, hM, hMδ⟩
  intro w hw
  exact stepDomain_margin hσ hσ1 hσs hw

/-- **Image** (`bpW:w5:flow`, step `f-image`): if `w ∈ D(s-5σ, ηr)` and the increment has
`|W|_r ≤ M ≤ σ η²/16` (`σ ≤ 1`, `η ≤ 1/8`), then `w + W ∈ D(s-4σ, 2ηr)`. -/
theorem stepImage_mem {s σ r η M : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hη : 0 < η)
    (hη8 : η ≤ 1 / 8) (hMσ : M ≤ σ * η ^ 2 / 16) {w W : KamPhase}
    (hw : w ∈ kamDomain (s - 5 * σ) (η * r)) (hW : kamNorm r W ≤ M) :
    w + W ∈ kamDomain (s - 4 * σ) (2 * η * r) := by
  obtain ⟨h1, h2, h3⟩ := hw
  unfold kamNorm at hW
  have n1 : 0 ≤ ‖W.1‖ := norm_nonneg _
  have n2 : 0 ≤ ‖W.2.1‖ / r ^ 2 := by positivity
  have n3 : 0 ≤ ‖W.2.2.1‖ / r := by positivity
  have n4 : 0 ≤ ‖W.2.2.2‖ / r := by positivity
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  have hsη : σ * η ^ 2 ≤ η ^ 2 := by nlinarith [sq_nonneg η]
  have hM0 : M ≤ η ^ 2 / 16 := by linarith
  have hM1 : M ≤ σ / 1024 := by nlinarith
  have hMη : M ≤ η / 128 := by nlinarith
  have c1 : ‖W.1‖ ≤ M := by linarith
  have c2 : ‖W.2.1‖ ≤ r ^ 2 * M := by
    have : ‖W.2.1‖ / r ^ 2 ≤ M := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have c3 : ‖W.2.2.1‖ + ‖W.2.2.2‖ ≤ r * M := by
    have : ‖W.2.2.1‖ / r + ‖W.2.2.2‖ / r ≤ M := by linarith
    rw [← add_div, div_le_iff₀ hr, mul_comm] at this
    exact this
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have him : ((w + W).1 i).im = (w.1 i).im + (W.1 i).im := by simp
    rw [him]
    have hi : |(W.1 i).im| ≤ ‖W.1‖ := (Complex.abs_im_le_norm _).trans (norm_le_pi_norm W.1 i)
    calc |(w.1 i).im + (W.1 i).im| ≤ |(w.1 i).im| + |(W.1 i).im| := abs_add_le _ _
      _ < (s - 5 * σ) + σ / 1024 := add_lt_add_of_lt_of_le (h1 i) (hi.trans (c1.trans hM1))
      _ < s - 4 * σ := by linarith
  · show ‖w.2.1 + W.2.1‖ < (2 * η * r) ^ 2
    have h4 := norm_add_le w.2.1 W.2.1
    have h5 : (η * r) ^ 2 = η ^ 2 * r ^ 2 := by ring
    have h6 : r ^ 2 * M ≤ r ^ 2 * (η ^ 2 / 16) := mul_le_mul_of_nonneg_left hM0 (by positivity)
    nlinarith [sq_nonneg r, sq_nonneg η, mul_nonneg (sq_nonneg η) (sq_nonneg r)]
  · show ‖w.2.2.1 + W.2.2.1‖ + ‖w.2.2.2 + W.2.2.2‖ < 2 * η * r
    have e1 := norm_add_le w.2.2.1 W.2.2.1
    have e2 := norm_add_le w.2.2.2 W.2.2.2
    have : r * M ≤ r * (η / 128) := mul_le_mul_of_nonneg_left hMη hr.le
    nlinarith

end KAM.Wave
