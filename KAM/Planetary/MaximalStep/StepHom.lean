/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepCoeff
public import KAM.Planetary.MaximalStep.Divisor
public import KAM.Planetary.MaximalStep.Constants
public import KAM.Planetary.MaximalStep.Parameter

/-!
# The homological stage of the canonical step (P11A-C8, `stepP:p11a:cs-hom`)

From the step hypotheses `P11StepHyp` this file derives the coefficient datum of the cutoff
(`p11_cutoff_coeff`), the divisor bound on `B` (`divisor_perturb`), and, for the generators
`φ_0 = stepP0` and `φ_{1,i} = stepP1 · i` given by `homological_maximal`, the angle-class,
the sup bounds `s A` and `A`, the average facts and the homological equation, for `A = p11StepA S`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

/-- The zeroth-order generator `φ_0(θ, b)`. -/
def stepP0 (S : P11Step n) (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ)
    (u : P11CVec n × P11CVec n) : ℂ := p11Solve S.T w (p11R0 S.T R) u.1 u.2

/-- The first-order generators `φ_{1,i}(θ, b)`. -/
def stepP1 (S : P11Step n) (w : P11CVec n → P11CVec n) (R : P11Family n → ℂ)
    (u : P11CVec n × P11CVec n) : P11CVec n :=
  fun i => p11Solve S.T w (fun z => p11R1 S.T R z i) u.1 u.2

variable {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ}

theorem step_B_open (S : P11Step n) : IsOpen (KAM.actionNbhd S.E S.t) :=
  p11_isOpen_actionNbhd S.E S.t

theorem step_r_pos (S : P11Step n) : 0 < S.r := by
  have := S.radius; have := S.d_pos; have := S.delta_pos; have := S.sigma_pos; linarith

theorem step_dr (S : P11Step n) : S.d < S.r := by
  have := S.radius; have := S.delta_pos; have := S.sigma_pos; linarith

theorem step_E_nonneg (S : P11Step n) : 0 ≤ p11Error n S.T S.d := by
  unfold p11Error
  have := p11C_ge_one S.n_pos
  have := S.d_pos
  positivity

theorem step_lambda_nonneg (S : P11Step n) : 0 ≤ p11Lambda n S.delta := by
  rw [← (p11_lambda_spec S.n_pos S.delta_pos).2.1]
  exact tsum_nonneg fun _ => (Real.exp_pos _).le

theorem step_A_nonneg (H : P11StepHyp S h w R) : 0 ≤ p11StepA S := by
  unfold p11StepA
  have := step_lambda_nonneg S; have := step_E_nonneg S; have := S.D_pos; have := S.s_pos
  have := S.eps_nonneg
  positivity

theorem step_small (S : P11Step n) : 4 * (n + 1) * p11StepA S ≤ S.sigma := by
  unfold p11StepA
  have hπ : 0 < Real.pi * S.D * S.s := by
    have := S.D_pos; have := S.s_pos; positivity
  rw [mul_div_assoc', div_le_iff₀ hπ]
  have := S.flow_small
  linarith

theorem step_hdiv (H : P11StepHyp S h w R) : ∀ b ∈ KAM.actionNbhd S.E S.t, ∀ k, k ≠ 0 →
    KAM.Fourier.modeSize k ≤ S.T → S.D / 2 ≤ ‖p11dotC k (w b)‖ :=
  divisor_perturb S.t_pos S.T_pos S.D_pos S.L_nonneg w H.holw H.derivative S.divisor_small
    H.divisor

theorem step_M_nonneg (S : P11Step n) : 0 ≤ (1 + p11Error n S.T S.d) * S.eps :=
  mul_nonneg (by linarith [step_E_nonneg S]) S.eps_nonneg

theorem step_hm0 (H : P11StepHyp S h w R) :
    p11AngleClass (S.r - S.d - S.delta) (KAM.actionNbhd S.E S.t) (stepP0 S w R) ∧
    p11Bound (KAM.complexStrip n (S.r - S.d - S.delta) ×ˢ KAM.actionNbhd S.E S.t)
      (stepP0 S w R) (S.s * p11StepA S) ∧
    DifferentiableOn ℂ (p11DeltaH S.T R) (KAM.actionNbhd S.E S.t) ∧
    p11Bound (KAM.actionNbhd S.E S.t) (p11DeltaH S.T R) ((1 + p11Error n S.T S.d) * S.eps) ∧
    ∀ θ ∈ KAM.complexStrip n (S.r - S.d - S.delta), ∀ b ∈ KAM.actionNbhd S.E S.t,
      fderiv ℂ (fun x => stepP0 S w R (x, b)) θ (w b) = p11R0 S.T R (θ, b) - p11DeltaH S.T R b := by
  have cc := p11_cutoff_coeff S.n_pos (step_r_pos S) S.s_pos S.T_pos.le S.d_pos (step_dr S)
    S.eps_nonneg (step_B_open S) H.admissible H.bound
  have hdel : S.delta < S.r - S.d := by have := S.radius; have := S.sigma_pos; linarith
  obtain ⟨c1, -, c3, -, c5, -, -⟩ := cc
  obtain ⟨h1, -, -, h4, -, h6, h7, -, h9, -⟩ := homological_maximal S.n_pos
    (by linarith [S.radius, S.delta_pos, S.sigma_pos]) S.delta_pos hdel S.T_pos S.D_pos
    (step_M_nonneg S) (step_B_open S) w H.holw (step_hdiv H) _ c1 c3 c5
  refine ⟨h1, fun z hz => (h7 z hz).trans (le_of_eq ?_), h4, h9, h6⟩
  have := S.D_pos; have := S.s_pos
  unfold p11StepA
  field_simp

end KAM.Planetary

end
