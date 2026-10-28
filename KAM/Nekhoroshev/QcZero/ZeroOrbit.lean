/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.QcZero.ZeroField
public import KAM.Nekhoroshev.ZeroPerturbation

/-!
# Zero perturbation: the integrable orbit solves the zero-perturbation flow

Blueprint `bpN:p2:zero` with receipts `z-init`, `z-ball`, `z-h`, `z-curve`, `z-eq`. For an
integrable `h` and a perturbation of size `0`, the affine orbit `t ↦ (θ₀ + t ω(I₀), I₀)`
starting at an action in `B(0, R/2)` stays in `W_s`, has a differentiable Hamiltonian along it,
and solves the real Hamiltonian system on `actionBall n R` for all times.
-/

public section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ}

section ZeroOrbit
variable {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
variable {h : (Fin n → ℂ) → ℂ} (hh : IsAnalyticIntegrable R s h)
variable {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
variable (hf : IsAnalyticPerturbation R s 0 f)
include hR hs hh hf

variable (theta0 I0 : Fin n → ℝ)

omit hR hs hh hf in
theorem z_init : integrableOrbit h theta0 I0 0 = (theta0, I0) ∧
    ∀ t : ℝ, (integrableOrbit h theta0 I0 t).2 = I0 := by
  exact ⟨by simp [integrableOrbit], fun t => rfl⟩

omit hs hh hf in
theorem z_ball (hI : I0 ∈ actionBall n (R / 2)) : I0 ∈ actionBall n R := by
  have : ‖I0‖ < R / 2 := by simpa [actionBall] using hI
  simp only [actionBall, Metric.mem_ball, dist_zero_right]
  linarith

theorem z_h (hI : I0 ∈ actionBall n (R / 2)) (t : ℝ) :
    (integrableOrbit h theta0 I0 t).2 ∈ actionBall n R ∧
    integrableOrbit h theta0 I0 t ∈ Wdom n R s ∧
    DifferentiableAt ℝ (KAM.realHamiltonian h f) (integrableOrbit h theta0 I0 t) := by
  have hIR : I0 ∈ actionBall n R := z_ball hR I0 hI
  have hW : integrableOrbit h theta0 I0 t ∈ Wdom n R s := by
    refine ⟨mem_univ _, ?_⟩
    have : ‖I0‖ < R := by simpa [actionBall] using hIR
    simp only [Metric.mem_ball, dist_zero_right]
    show ‖I0‖ < R + s
    linarith
  exact ⟨hIR, hW, (zero_deriv hR hs hh hf _ hW).2.1⟩

omit hR hs hh hf in
theorem z_curve (t : ℝ) : HasDerivAt (integrableOrbit h theta0 I0)
    (KAM.frequencyMap h I0, 0) t := by
  have h0 : HasDerivAt (fun t : ℝ => t • KAM.frequencyMap h I0) (KAM.frequencyMap h I0) t := by
    simpa using (hasDerivAt_id' t).smul_const (KAM.frequencyMap h I0)
  exact (h0.const_add theta0).prodMk (hasDerivAt_const t I0)

theorem z_eq (hI : I0 ∈ actionBall n (R / 2)) :
    IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) Set.univ
      (integrableOrbit h theta0 I0) :=
  (zero_perturbation_core hR hs hh hf theta0 I0 hI).2.1

/-- Exact conclusion already proved by `zero_perturbation_core`. -/
theorem zero (hI : I0 ∈ actionBall n (R / 2)) :
    integrableOrbit h theta0 I0 0 = (theta0, I0) ∧
    IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) Set.univ
      (integrableOrbit h theta0 I0) ∧
    ∀ t : ℝ, (integrableOrbit h theta0 I0 t).2 = I0 :=
  zero_perturbation_core hR hs hh hf theta0 I0 hI

end ZeroOrbit

end KAM.Nekhoroshev
