/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationBridge

/-! # P11B iteration: parameter Cauchy for vector-valued maps and the real collar supplier

`param_cauchy_gen` is `param_cauchy` for maps with values in any complex Banach space (the joint
angle-action defect), valid also for `j = 0`. `step_real_lipschitz_collar` is the real
angle-derivative estimate of `canonical_step_real` for every real parameter in the collar
`E + t`, not only for `b ∈ E` (the supplier required by `SelectionIteration.real_angle_derivative`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem param_cauchy_gen {E : Set (P11Vec n)} {t tp M : ℝ} {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [SecondCountableTopology W]
    (htp : 0 < tp) (ht : tp < t) {u : P11CVec n → W}
    (hu : DifferentiableOn ℂ u (KAM.actionNbhd E t))
    (hb : ∀ b ∈ KAM.actionNbhd E t, ‖u b‖ ≤ M) (j : ℕ) :
    ∀ b ∈ KAM.actionNbhd E tp, ‖iteratedFDeriv ℂ j u b‖ ≤ (j : ℝ) ^ j * M / (t - tp) ^ j := by
  intro b hb'
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hmem : b ∈ KAM.actionNbhd E t := by
      obtain ⟨J, hJ, hbJ⟩ := hb'
      exact ⟨J, hJ, hbJ.trans ht⟩
    simpa using hb b hmem
  obtain ⟨J, hJ, hbJ⟩ := hb'
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hδ : 0 < (t - tp) / j := div_pos (by linarith) hjpos
  have hball : Metric.closedBall b (j * ((t - tp) / j)) ⊆ KAM.actionNbhd E t := by
    intro w hw
    refine ⟨J, hJ, ?_⟩
    have hw' := mem_closedBall_iff_norm.mp hw
    rw [mul_div_cancel₀ _ hjpos.ne'] at hw'
    calc ‖w - fun i => (J i : ℂ)‖ = ‖(w - b) + (b - fun i => (J i : ℂ))‖ := by
          congr 1; abel
      _ ≤ ‖w - b‖ + ‖b - fun i => (J i : ℂ)‖ := norm_add_le _ _
      _ < t := by linarith
  have := p11_norm_iteratedFDeriv_le_of_closedBall (p11_isOpen_actionNbhd E t) hδ j hu hball
    (fun w hw => hb w (hball hw))
  convert this using 1
  rw [div_pow, div_div_eq_mul_div]
  ring

variable {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ}

/-- `canonical_step_real`'s Lipschitz clause for every real parameter of the collar `E + t`. -/
theorem step_real_lipschitz_collar (H : P11StepHyp S h w R)
    {b : P11Vec n} (hb : KAM.realInclusion n b ∈ KAM.actionNbhd S.E S.t) (θ : P11Vec n)
    (hreal : p11Real (domain_def n S.r S.s (KAM.actionNbhd S.E S.t)) R) :
    ‖fderiv ℝ (fun x : P11Vec n => fun i =>
      ((p11StepMap S w R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).1 i).re) θ -
      ContinuousLinearMap.id ℝ _‖ ≤
      Real.exp (2 * S.T * (1 + p11Error n S.T S.d) * S.eps * p11Lambda n (S.r - S.d) /
        (S.D * S.s)) - 1 := by
  have hD := S.D_pos
  have hs := S.s_pos
  have hr : 0 < S.r - S.d := by linarith [step_dr S]
  have hΛ : 0 ≤ p11Lambda n (S.r - S.d) := by
    rw [← (p11_lambda_spec S.n_pos hr).2.1]
    exact tsum_nonneg fun _ => (Real.exp_pos _).le
  have hL : 0 ≤ 2 * S.T * ((1 + p11Error n S.T S.d) * S.eps / S.s) *
      p11Lambda n (S.r - S.d) / S.D := by
    have := step_M_nonneg S; have := S.T_pos; positivity
  have key := real_lipschitz (stepV_contDiff S w R b) (step_A_nonneg H) hL
    (stepV_bound H hb) (stepV_fderiv H hb) (fun x k => stepV_periodic H hb x k) 1
    ⟨by norm_num, le_rfl⟩ θ
  have e : (fun x : P11Vec n => fun i =>
      ((p11StepMap S w R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).1 i).re) =
      p11RealFlow (stepV S w R b) 1 := funext fun x => step_flow_real H hreal hb x
  rw [e]
  refine key.1.trans (le_of_eq ?_)
  congr 2
  field_simp

end KAM.Planetary

end
