/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.AnalyticTaylor
public import KAM.Planetary.PGAssembly.JetsPolar
public import KAM.Planetary.Preparation.PolarAverage.Order

/-!
# Vanishing jets from a quartic growth bound (P11A-P7 helper)

`p11_jets_vanish_of_pow_bound`: a holomorphic `F` on a ball around `0` of a finite-dimensional
complex normed space with `‖F z‖ ≤ M ‖z‖ ^ 4` has `iteratedFDeriv ℂ j F 0 = 0` for `j < 4`.
Along each complex line the one-variable `p11_vanish_of_decay` applies; the symmetric
multilinear jet then vanishes by polarization (`eq_zero_of_diag_of_symm`, applied to the real
and imaginary parts of the real-restricted jet).
-/

@[expose] public noncomputable section
open Set Metric
namespace KAM.Planetary

section Jets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Polarization for a complex symmetric multilinear form. -/
theorem p11_eq_zero_of_diag_of_symm (k : ℕ)
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ)
    (hs : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E), M (v ∘ σ) = M v)
    (hd : ∀ y, M (fun _ => y) = 0) : M = 0 := by
  have key : ∀ L : ℂ →L[ℝ] ℝ, L.compContinuousMultilinearMap (M.restrictScalars ℝ) = 0 :=
    fun L => eq_zero_of_diag_of_symm k _ (fun σ v => by simp [hs σ v]) (fun y => by simp [hd y])
  ext v
  have h1 := congrArg (fun N => N v) (key Complex.reCLM)
  have h2 := congrArg (fun N => N v) (key Complex.imCLM)
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.coe_restrictScalars, ContinuousMultilinearMap.zero_apply,
    Complex.reCLM_apply, Complex.imCLM_apply] at h1 h2
  exact Complex.ext (by simpa using h1) (by simpa using h2)

theorem p11_jets_vanish_of_pow_bound {F : E → ℂ} {r M : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball 0 r)) (hb : ∀ z ∈ ball (0 : E) r, ‖F z‖ ≤ M * ‖z‖ ^ 4) :
    ∀ j < 4, iteratedFDeriv ℂ j F 0 = 0 := by
  intro j hj
  have hcd : ContDiffAt ℂ ⊤ F 0 :=
    (KAM.analyticOnNhd_of_differentiableOn isOpen_ball hF 0 (mem_ball_self hr)).contDiffAt
  refine p11_eq_zero_of_diag_of_symm j _ (fun σ v => hcd.iteratedFDeriv_comp_perm v σ)
    (fun y => ?_)
  rw [← KAM.iteratedDeriv_line_eq_iteratedFDeriv isOpen_ball hF (mem_ball_self hr) y j]
  by_cases hy : y = 0
  · subst hy
    have h0 : F 0 = 0 := by
      have := hb 0 (mem_ball_self hr)
      simpa using this
    simp only [zero_add, smul_zero, h0]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · simp [iteratedDeriv_const, hj0.ne']
  · have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy
    set R : ℝ := r / ‖y‖ with hR
    have hR0 : 0 < R := div_pos hr hyp
    have hline : ∀ ζ ∈ ball (0 : ℂ) R, 0 + ζ • y ∈ ball (0 : E) r := by
      intro ζ hζ
      rw [zero_add, mem_ball_zero_iff, norm_smul]
      have := mem_ball_zero_iff.mp hζ
      rwa [hR, lt_div_iff₀ hyp] at this
    have hg : DifferentiableOn ℂ (fun ζ : ℂ => F (0 + ζ • y)) (ball 0 R) :=
      hF.comp (by fun_prop : DifferentiableOn ℂ (fun ζ : ℂ => (0 : E) + ζ • y) _) hline
    have := p11_vanish_of_decay (C := M * ‖y‖ ^ 4) (k := 8) hR0 hg (fun t ht0 htR => by
      have htb : (t : ℂ) ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        exact htR
      have h1 := hb _ (hline (t : ℂ) htb)
      rw [zero_add, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht0.le] at h1
      have e : Real.sqrt t ^ 8 = t ^ 4 := by
        rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt ht0.le]
      rw [e]
      calc _ ≤ M * (t * ‖y‖) ^ 4 := by simpa [zero_add] using h1
        _ = _ := by ring) j (by omega)
    exact this

end Jets

end KAM.Planetary

end
