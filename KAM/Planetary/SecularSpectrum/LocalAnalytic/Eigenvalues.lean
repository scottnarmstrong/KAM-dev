/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Analytic

/-!
# Secular spectrum: analytic eigenvalue branches

Blueprint P, Part 9 (`bpP:p9:e-ift`, `stepP:p9:la-ev`).  The parameter version of the analytic
implicit function theorem for a scalar equation `f (w, s) = 0` with `∂ₛ f ≠ 0`, and its use for
`f (w, s) = det (s - M w)` at a simple eigenvalue: each simple root of the characteristic
polynomial of `M w₀` continues to an analytic branch `σ_j`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise ContDiff
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section IFT
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Analytic implicit function theorem for a scalar equation (`bpP:p9:e-ift`). -/
theorem exists_analytic_root {f : E × ℝ → ℝ} {w0 : E} {s0 : ℝ}
    (hf : AnalyticAt ℝ f (w0, s0)) (h0 : f (w0, s0) = 0) {c : ℝ}
    (hc : HasDerivAt (fun s => f (w0, s)) c s0) (hc0 : c ≠ 0) :
    ∃ σ : E → ℝ, AnalyticAt ℝ σ w0 ∧ σ w0 = s0 ∧ ∀ᶠ w in 𝓝 w0, f (w, σ w) = 0 := by
  have hcd : ContDiffAt ℝ ω f (w0, s0) := hf.contDiffAt
  have hpn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hderiv : HasFDerivAt f (fderiv ℝ f (w0, s0)) (w0, s0) :=
    (hcd.differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => (w0, t)) ((0 : E), (1 : ℝ)) s0 :=
    (hasDerivAt_const s0 w0).prodMk (hasDerivAt_id s0)
  have h3 := (hderiv.comp_hasDerivAt s0 hg).unique hc
  have hL : (fderiv ℝ f (w0, s0) ∘L .inr ℝ E ℝ) = c • (1 : ℝ →L[ℝ] ℝ) := by
    ext
    simpa using h3
  have hinv : (fderiv ℝ f (w0, s0) ∘L .inr ℝ E ℝ).IsInvertible := by
    rw [hL]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := c⁻¹ • (1 : ℝ →L[ℝ] ℝ)) ?_ ?_
    · ext; simp [hc0]
    · ext; simp [hc0]
  refine ⟨hcd.implicitFunction hpn hinv, (hcd.contDiffAt_implicitFunction hpn hinv).analyticAt,
    hcd.implicitFunction_apply_self hpn hinv, ?_⟩
  filter_upwards [hcd.eventually_apply_implicitFunction hpn hinv] with x hx
  rwa [h0] at hx

end IFT

section Det
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E}

lemma analyticAt_det {A : E → Mat n} (hA : AnalyticAt ℝ A w) :
    AnalyticAt ℝ (fun x => (A x).det) w := by
  simp_rw [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => analyticAt_mat_entry hA (σ i) i

lemma det_shift_eq_eval (M : Mat n) (s : ℝ) :
    (s • (1 : Mat n) - M).det = M.charpoly.eval s := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Det

section Branch
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Each simple root `σ0 j` of `charpoly (M w0)` continues to an analytic branch of roots of
`charpoly (M w)` (`stepP:p9:la-ev`, first half). -/
theorem exists_eigenvalue_branch {M : E → Mat n} {w0 : E} (hM : AnalyticAt ℝ M w0)
    {σ0 : Vec n} (hσ0 : Function.Injective σ0)
    (hch : (M w0).charpoly = ∏ k, (X - C (σ0 k))) (j : Fin n) :
    ∃ s : E → ℝ, AnalyticAt ℝ s w0 ∧ s w0 = σ0 j ∧
      ∀ᶠ w in 𝓝 w0, (M w).charpoly.eval (s w) = 0 := by
  set f : E × ℝ → ℝ := fun x => (x.2 • (1 : Mat n) - M x.1).det with hf
  have hroot : (M w0).charpoly.eval (σ0 j) = 0 := by
    rw [hch, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  have hfa : AnalyticAt ℝ f (w0, σ0 j) := by
    refine analyticAt_det ?_
    refine analyticAt_pi_iff.2 fun a => analyticAt_pi_iff.2 fun b => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (analyticAt_snd.mul analyticAt_const).sub
      (AnalyticAt.fun_comp (g := fun y => M y a b) (f := fun x : E × ℝ => x.1)
        (analyticAt_mat_entry hM a b) analyticAt_fst)
  have hfun : (fun s => f (w0, s)) = fun s => (M w0).charpoly.eval s := by
    funext s; simp [hf, det_shift_eq_eval]
  have hsep : (M w0).charpoly.Separable := by
    rw [hch]; exact Polynomial.separable_prod_X_sub_C_iff.2 hσ0
  have hc0 : (M w0).charpoly.derivative.eval (σ0 j) ≠ 0 := by
    have := hsep.aeval_derivative_ne_zero (x := σ0 j) (by simpa using hroot)
    simpa using this
  obtain ⟨s, hs, hs0, hev⟩ := exists_analytic_root hfa (by simp [hf, det_shift_eq_eval, hroot])
    (c := (M w0).charpoly.derivative.eval (σ0 j))
    (by rw [hfun]; exact (M w0).charpoly.hasDerivAt (σ0 j)) hc0
  exact ⟨s, hs, hs0, by simpa [hf, det_shift_eq_eval] using hev⟩

end Branch

end SecularSpectrum

end KAM.Planetary
