/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.AnalyticTaylor
public import KAM.Strip.Cauchy
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Decay of iterated derivatives on inner strips (support for `fourier_compact`)

If a sequence `H j` of holomorphic functions on the strip of width `w` tends to `0` uniformly on
every strip of width `ρ < w`, then every iterated Fréchet derivative `D^m (H j)` also tends to `0`
uniformly on every such strip. One step is the first-order Cauchy estimate on a ball of radius
`(w - ρ) / 2`; the induction passes through `D^{m+1} f = D (D^m f)` (up to an isometry), the
derivatives `D^m (H j)` being holomorphic as `H j` is analytic on the open strip.
-/

@[expose] public section

open Set Filter Metric

namespace KAM

variable {n : ℕ}

/-- A real function sequence tends to `0` uniformly on every strip of width `ρ < w`. -/
def StripDecay (n : ℕ) (w : ℝ) (φ : ℕ → (Fin n → ℂ) → ℝ) : Prop :=
  ∀ ρ < w, ∀ ε > 0, ∀ᶠ j in atTop, ∀ z ∈ complexStrip n ρ, φ j z < ε

/-- One Cauchy step: decay of `g j` on inner strips gives decay of `D (g j)`. -/
theorem stripDecay_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {w : ℝ}
    {g : ℕ → (Fin n → ℂ) → V} (hg : ∀ j, DifferentiableOn ℂ (g j) (complexStrip n w))
    (h : StripDecay n w fun j z => ‖g j z‖) :
    StripDecay n w fun j z => ‖fderiv ℂ (g j) z‖ := by
  intro ρ hρ ε hε
  obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ' = (ρ + w) / 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = ρ' - ρ := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef, hρ']; linarith
  have hρ'w : ρ' < w := by rw [hρ']; linarith
  filter_upwards [h ρ' hρ'w (ε * δ / 2) (by positivity)] with j hj z hz
  have hsub : closedBall z δ ⊆ complexStrip n ρ' := by
    intro θ hθ i
    have h1 : ‖θ i - z i‖ ≤ δ :=
      (norm_le_pi_norm (θ - z) i).trans (by simpa [dist_eq_norm] using hθ)
    have h2 : |(θ i).im - (z i).im| ≤ δ := by
      simpa [Complex.sub_im] using (Complex.abs_im_le_norm (θ i - z i)).trans h1
    have h3 := hz i
    calc |(θ i).im| = |(z i).im + ((θ i).im - (z i).im)| := by rw [add_sub_cancel]
      _ ≤ |(z i).im| + |(θ i).im - (z i).im| := abs_add_le _ _
      _ < ρ' := by linarith
  have hsub' : closedBall z δ ⊆ complexStrip n w := hsub.trans fun θ hθ i => (hθ i).trans hρ'w
  have := norm_fderiv_le_of_closedBall_bound (isOpen_complexStrip n w) (hg j) hδ hsub'
    (fun θ hθ => (hj θ (hsub hθ)).le)
  refine this.trans_lt ?_
  rw [div_lt_iff₀ hδ]
  nlinarith [mul_pos hε hδ]

/-- Decay of all iterated Fréchet derivatives on inner strips. -/
theorem stripDecay_iteratedFDeriv {w : ℝ} {H : ℕ → (Fin n → ℂ) → ℂ}
    (hH : ∀ j, DifferentiableOn ℂ (H j) (complexStrip n w))
    (h0 : StripDecay n w fun j z => ‖H j z‖) (m : ℕ) :
    StripDecay n w fun j z => ‖iteratedFDeriv ℂ m (H j) z‖ := by
  induction m with
  | zero => simpa only [norm_iteratedFDeriv_zero] using h0
  | succ m ih =>
    have han : ∀ j, DifferentiableOn ℂ (iteratedFDeriv ℂ m (H j)) (complexStrip n w) := fun j =>
      ((analyticOnNhd_of_differentiableOn (isOpen_complexStrip n w) (hH j)).iteratedFDeriv_of_isOpen
        (isOpen_complexStrip n w) m).differentiableOn
    simpa only [norm_fderiv_iteratedFDeriv] using stripDecay_fderiv han ih

end KAM

end
