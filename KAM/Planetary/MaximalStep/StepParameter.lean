/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Step

/-!
# Parameter derivatives of the canonical step (P11A-C8, `stepP:p11a:cs-param`)

`canonical_step_param`: Cauchy estimates in the parameter (`param_cauchy`), applied for each fixed
point of `D_+` to `ΔH`, `ΔW`, the displacements and the remainder, with the bounds of
`canonical_step`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

theorem step_slice_diff {n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {G : P11Family n → W} {r s : ℝ} {B : Set (P11CVec n)}
    (hG : DifferentiableOn ℂ G (domain_def n r s B)) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} s r) : DifferentiableOn ℂ (fun b => G (z, b)) B :=
  hG.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun b hb => ⟨hz, hb⟩

/-- v: use the existing full complex domain; derivatives cost only t-tp. -/
theorem canonical_step_param {n : ℕ} {S : P11Step n} {h : P11CVec n → ℂ}
    {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ} (H : P11StepHyp S h w R)
    {tp : ℝ} (htp : 0 < tp) (ht : tp < S.t) {j : ℕ} (hj : 1 ≤ j) :
    ∀ b ∈ KAM.actionNbhd S.E tp,
      ‖iteratedFDeriv ℂ j (p11DeltaH S.T R) b‖ ≤
        (j : ℝ)^j*(1+p11Error n S.T S.d)*S.eps/(S.t-tp)^j ∧
      ‖iteratedFDeriv ℂ j (p11DeltaW S.T R) b‖ ≤
        (j : ℝ)^j*(1+p11Error n S.T S.d)*S.eps/(S.s*(S.t-tp)^j) ∧
      ∀ z ∈ KAM.Weighted.Dom n {0} (S.q*S.s) (S.r-S.d-S.delta-2*S.sigma),
        ‖iteratedFDeriv ℂ j (fun b => (p11StepMap S w R (z,b)).1-z.1) b‖ ≤
          (j : ℝ)^j*p11StepA S/(S.t-tp)^j ∧
        ‖iteratedFDeriv ℂ j (fun b => (p11StepMap S w R (z,b)).2-z.2) b‖ ≤
          (j : ℝ)^j*(n+1)*S.s*p11StepA S/(S.sigma*(S.t-tp)^j) ∧
        (∀ Mr : ℝ, p11Bound
          (domain_def n (S.r-S.d-S.delta-2*S.sigma) (S.q*S.s) (KAM.actionNbhd S.E S.t))
          (p11StepRemainder S h w R) Mr →
          ‖iteratedFDeriv ℂ j (fun b => p11StepRemainder S h w R (z,b)) b‖ ≤
            (j : ℝ)^j*Mr/(S.t-tp)^j) := by
  intro b hb
  have cs := canonical_step H
  obtain ⟨hdH, hdW, hbH, hbW, hF, -, hdisp, -⟩ := cs
  have hs := S.s_pos
  have hσ := S.sigma_pos
  have hjt : 0 < (S.t - tp) ^ j := pow_pos (by linarith) j
  have hA := step_A_nonneg H
  refine ⟨?_, ?_, fun z hz => ⟨?_, ?_, fun Mr hMr => ?_⟩⟩
  · refine (param_cauchy_scalar htp ht hdH hbH hj b hb).trans (le_of_eq ?_)
    ring
  · refine (param_cauchy htp ht (div_nonneg (step_M_nonneg S) hs.le) hdW hbW hj b hb).trans (le_of_eq ?_)
    field_simp
  · have hd : DifferentiableOn ℂ (fun b => (p11StepMap S w R (z, b)).1 - z.1)
        (KAM.actionNbhd S.E S.t) :=
      ((differentiable_fst.comp_differentiableOn (step_slice_diff hF hz))).sub_const _
    refine (param_cauchy htp ht hA hd (fun b' hb' => (hdisp (z, b') ⟨hz, hb'⟩).1) hj b hb).trans
      (le_of_eq ?_)
    ring
  · have hd : DifferentiableOn ℂ (fun b => (p11StepMap S w R (z, b)).2 - z.2)
        (KAM.actionNbhd S.E S.t) :=
      ((differentiable_snd.comp_differentiableOn (step_slice_diff hF hz))).sub_const _
    have hM : 0 ≤ (n + 1) * S.s * p11StepA S / S.sigma := by positivity
    refine (param_cauchy htp ht hM hd (fun b' hb' => (hdisp (z, b') ⟨hz, hb'⟩).2) hj b hb).trans
      (le_of_eq ?_)
    field_simp
  · have hd := step_slice_diff (step_Rp_admissible H).1 hz
    have hM : 0 ≤ Mr := by
      obtain ⟨J, hJ, hbJ⟩ := hb
      have hb' : b ∈ KAM.actionNbhd S.E S.t := ⟨J, hJ, by
        have := S.t_pos; have : ‖b - fun i => (J i : ℂ)‖ < S.t := by linarith [hbJ]
        exact this⟩
      exact (norm_nonneg _).trans (hMr (z, b) ⟨hz, hb'⟩)
    exact param_cauchy_scalar htp ht (u := fun b => p11StepRemainder S h w R (z, b)) hd
      (fun b' hb' => hMr (z, b') ⟨hz, hb'⟩) hj b hb
