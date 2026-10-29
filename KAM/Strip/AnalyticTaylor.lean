/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Regularity
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Holomorphic maps on finite-dimensional complex spaces are analytic

Mathlib proves `DifferentiableOn.analyticOnNhd` only for functions of one complex variable. This
file proves the finite-dimensional statement for a map `f : E → W` that is complex differentiable
on an open set `U`, with `E` finite-dimensional and `W` a complete second-countable complex normed
space (the hypotheses of `KAM.contDiffOn_infty_of_differentiableOn`).

The proof combines three ingredients.

* **Regularity.** `f` is smooth on `U` and every `D^j f` is holomorphic
  (`KAM.contDiffOn_infty_of_differentiableOn`, `KAM/Strip/Regularity.lean`).
* **Iterated Cauchy estimate.** `n` applications of the first-order Cauchy estimate on nested
  polydiscs of radius `ρ / n` give `‖D^n f (z)‖ ≤ (n / ρ)^n A`, hence the Taylor series
  `∑ (n!)⁻¹ D^n f(z) h^n` has radius of convergence at least `ρ / e`
  (`KAM.norm_iteratedFDeriv_le_of_closedBall`).
* **Taylor expansion along lines.** For `‖h‖ < ρ / e` the restriction `s ↦ f (z + s • h)` is
  holomorphic on a disc of radius `2`, so Mathlib's one-variable Taylor theorem
  (`Complex.hasSum_taylorSeries_on_ball`) sums the series to `f (z + h)`; the Taylor coefficient
  of the restriction is the diagonal value of `D^n f (z)`
  (`KAM.iteratedDeriv_line_eq_iteratedFDeriv`).

The result is `KAM.analyticOnNhd_of_differentiableOn`, and the same Taylor-along-lines argument is
reused for the multi-index power series of `KAM/Strip/AnalyticSeries.lean`.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff

namespace KAM

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The Taylor series of `f` at `z`: its `n`-th term is `(n!)⁻¹ • D^n f (z)`. -/
def taylorSeriesAt (f : E → W) (z : E) : FormalMultilinearSeries ℂ E W :=
  fun n => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f z

theorem taylorSeriesAt_apply (f : E → W) (z : E) (n : ℕ) (y : E) :
    taylorSeriesAt f z n (fun _ => y) =
      ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f z (fun _ => y) := rfl

variable [FiniteDimensional ℂ E]

/-- Blueprint `step:p1:han-margin`. A closed ball contained in an open set `U` can be enlarged
inside `U`, and a function continuous on `U` (here: holomorphic) is bounded on the closed ball. -/
theorem han_margin {U : Set E} (hU : IsOpen U) {f : E → W} (hf : DifferentiableOn ℂ f U)
    {z : E} {r : ℝ} (hr : 0 < r) (hz : closedBall z r ⊆ U) :
    (∃ r₁ > r, closedBall z r₁ ⊆ U) ∧ ∃ A : ℝ, ∀ w ∈ closedBall z r, ‖f w‖ ≤ A := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he, hthick⟩ := (isCompact_closedBall z r).exists_thickening_subset_open hU hz
    rw [thickening_closedBall he hr.le] at hthick
    exact ⟨r + e / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hthick⟩
  · obtain ⟨A, hA⟩ := ((isCompact_closedBall z r).image_of_continuousOn
      (hf.continuousOn.mono hz)).isBounded.exists_norm_le
    exact ⟨A, fun w hw => hA _ (mem_image_of_mem f hw)⟩

variable [CompleteSpace W] [SecondCountableTopology W]

/-- Every iterated Fréchet derivative of a holomorphic map is holomorphic. -/
theorem differentiableOn_iteratedFDeriv_of_isOpen {U : Set E} (hU : IsOpen U) {f : E → W}
    (hf : DifferentiableOn ℂ f U) (j : ℕ) : DifferentiableOn ℂ (iteratedFDeriv ℂ j f) U := by
  have hs := contDiffOn_infty_of_differentiableOn hU hf
  exact (hs.differentiableOn_iteratedFDerivWithin (by exact_mod_cast ENat.natCast_lt_top j)
    hU.uniqueDiffOn).congr fun x hx => (iteratedFDerivWithin_of_isOpen j hU hx).symm

/-- The `k`-th derivative of the restriction of a holomorphic map to the complex line
`s ↦ w + s • v` at `s = 0` is the diagonal value of `D^k f (w)`. -/
theorem iteratedDeriv_line_eq_iteratedFDeriv {U : Set E} (hU : IsOpen U) {f : E → W}
    (hf : DifferentiableOn ℂ f U) {w : E} (hw : w ∈ U) (v : E) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => f (w + s • v)) 0 = iteratedFDeriv ℂ k f w (fun _ => v) := by
  have hs := contDiffOn_infty_of_differentiableOn hU hf
  set G : E → W := fun x => f (w + x) with hG
  set U' : Set E := (fun x => w + x) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hGs : ContDiffOn ℂ ∞ G U' := hs.comp (contDiff_const.add contDiff_id).contDiffOn
    (fun x hx => hx)
  let g : ℂ →L[ℂ] E := (1 : ℂ →L[ℂ] ℂ).smulRight v
  have hg : ∀ s, g s = s • v := fun s => by simp [g]
  have hfun : (fun s : ℂ => f (w + s • v)) = G ∘ g := by
    ext s; simp [G, hg]
  have h0 : g 0 ∈ U' := by simpa [hU', hg] using hw
  have hgU : UniqueDiffOn ℂ (g ⁻¹' U') := (hU'o.preimage g.continuous).uniqueDiffOn
  have hopen : IsOpen (g ⁻¹' U') := hU'o.preimage g.continuous
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun, ← iteratedFDerivWithin_of_isOpen k hopen h0,
    g.iteratedFDerivWithin_comp_right hGs hU'o.uniqueDiffOn hgU h0 (by exact_mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg, one_smul]
  rw [iteratedFDerivWithin_of_isOpen k hU'o (by simpa [hg] using h0), hG,
    iteratedFDeriv_comp_add_left]
  simp

/-- Iterated Cauchy estimate for the full Fréchet derivative of order `n` on a closed ball:
`n` steps of the first-order estimate on nested polydiscs of radius `ρ / n`. -/
theorem norm_iteratedFDeriv_le_of_closedBall {U : Set E} (hU : IsOpen U) {f : E → W}
    (hf : DifferentiableOn ℂ f U) {z : E} {ρ A : ℝ} (hρ : 0 < ρ) (hz : closedBall z ρ ⊆ U)
    (hA : ∀ w ∈ closedBall z ρ, ‖f w‖ ≤ A) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f z‖ ≤ (n / ρ) ^ n * A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hA z (mem_closedBall_self hρ.le)
  have hδ : 0 < ρ / n := by positivity
  have key : ∀ j ≤ n, ∀ y ∈ closedBall z (ρ - j * (ρ / n)),
      ‖iteratedFDeriv ℂ j f y‖ ≤ (ρ / n)⁻¹ ^ j * A := by
    intro j
    induction j with
    | zero => intro _ y hy; simpa using hA y (by simpa using hy)
    | succ j ih =>
      intro hj y hy
      have hsub : closedBall y (ρ / n) ⊆ closedBall z (ρ - j * (ρ / n)) := by
        refine closedBall_subset_closedBall' ?_
        rw [mem_closedBall] at hy
        push_cast at hy
        linarith
      have hsubU : closedBall z (ρ - j * (ρ / n)) ⊆ closedBall z ρ :=
        closedBall_subset_closedBall (by
          have : (0 : ℝ) ≤ j * (ρ / n) := by positivity
          linarith)
      have hd := norm_fderiv_le_of_closedBall_bound hU
        (differentiableOn_iteratedFDeriv_of_isOpen hU hf j) hδ
        ((hsub.trans hsubU).trans hz)
        (fun w hw => ih (Nat.le_of_succ_le hj) w (hsub hw))
      rw [norm_fderiv_iteratedFDeriv] at hd
      calc ‖iteratedFDeriv ℂ (j + 1) f y‖ ≤ _ := hd
        _ = (ρ / n)⁻¹ ^ (j + 1) * A := by rw [pow_succ]; field_simp
  have h := key n le_rfl z (by
    have : (n : ℝ) * (ρ / n) = ρ := by field_simp
    simp [this])
  simpa [inv_div] using h

/-- The Taylor series of a holomorphic map converges to it on the ball of radius `ρ / e` around
`z`, where `ρ` is the radius of a closed ball inside the domain. -/
theorem hasFPowerSeriesOnBall_taylorSeriesAt {U : Set E} (hU : IsOpen U) {f : E → W}
    (hf : DifferentiableOn ℂ f U) {z : E} {ρ A : ℝ} (hρ : 0 < ρ) (hz : closedBall z ρ ⊆ U)
    (hA : ∀ w ∈ closedBall z ρ, ‖f w‖ ≤ A) :
    HasFPowerSeriesOnBall f (taylorSeriesAt f z) z ((ρ / Real.exp 1).toNNReal : ENNReal) := by
  have hzU : z ∈ U := hz (mem_closedBall_self hρ.le)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA z (mem_closedBall_self hρ.le))
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  have hr0 : 0 < ρ / Real.exp 1 := by positivity
  refine ⟨?_, by simpa using hr0, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ A fun n => ?_
    rw [Real.coe_toNNReal _ hr0.le]
    have h1 := norm_iteratedFDeriv_le_of_closedBall hU hf hρ hz hA n
    have h2 : (n : ℝ) ^ n / n.factorial ≤ Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul, mul_one]
      exact Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg n) n
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    calc ‖taylorSeriesAt f z n‖ * (ρ / Real.exp 1) ^ n
        = (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f z‖ * (ρ / Real.exp 1) ^ n := by
          simp [taylorSeriesAt, norm_smul]
      _ ≤ (n.factorial : ℝ)⁻¹ * ((n / ρ) ^ n * A) * (ρ / Real.exp 1) ^ n := by gcongr
      _ = ((n : ℝ) ^ n / n.factorial) / Real.exp 1 ^ n * A := by
          rw [div_pow, div_pow]; field_simp
      _ ≤ 1 * A := by
          gcongr
          rw [div_le_one (by positivity)]
          exact h2
      _ = A := one_mul A
  · intro y hy
    have hy' : ‖y‖ < ρ / Real.exp 1 := by
      have h1 : ENNReal.ofReal ‖y‖ < ENNReal.ofReal (ρ / Real.exp 1) := by
        rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
        exact hy
      exact (ENNReal.ofReal_lt_ofReal_iff hr0).mp h1
    have hy2 : ‖y‖ < ρ / 2 := by
      refine hy'.trans_le ?_
      gcongr
    have hmaps : MapsTo (fun s : ℂ => z + s • y) (ball 0 2) (closedBall z ρ) := by
      intro s hs
      rw [mem_ball_zero_iff] at hs
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      calc ‖s‖ * ‖y‖ ≤ 2 * (ρ / 2) := by gcongr
        _ = ρ := by ring
    have hφ : DifferentiableOn ℂ (fun s : ℂ => f (z + s • y)) (ball 0 2) :=
      hf.comp ((differentiable_id.smul_const y).const_add z).differentiableOn
        (fun s hs => hz (hmaps hs))
    have h1 : (1 : ℂ) ∈ ball 0 2 := by simp
    have := Complex.hasSum_taylorSeries_on_ball hφ h1
    simpa [taylorSeriesAt_apply, iteratedDeriv_line_eq_iteratedFDeriv hU hf hzU y] using this

/-- **Holomorphic maps on open subsets of a finite-dimensional complex space are analytic.**
Mathlib's `DifferentiableOn.analyticOnNhd` is the case `E = ℂ`. -/
theorem analyticOnNhd_of_differentiableOn {U : Set E} (hU : IsOpen U) {f : E → W}
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  intro z hz
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨ρ, hρ, hρU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  obtain ⟨A, hA⟩ := (han_margin hU hf hρ hρU).2
  exact (hasFPowerSeriesOnBall_taylorSeriesAt hU hf hρ hρU hA).analyticAt

end KAM
