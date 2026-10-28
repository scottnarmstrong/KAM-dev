/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularForm.AnalyticGeometry

/-!
# Quadratic part: analytic dependence of the coefficients on the action

Blueprint P, Part 8, `stepP:p8:qf-assembly` (package S8-Q). The map `Λ ↦ axis D Λ` is analytic and
sends a neighbourhood of `action D a` into `axes n`; the constant term and the quadratic form are
analytic in `(ξ, Λ, η)` through `axis`.
-/

@[expose] public noncomputable section
open Set Filter Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

theorem analyticAt_axis (D : Data n) (Λ : Vec n) : AnalyticAt ℝ (axis D) Λ := by
  refine analyticAt_pi_iff.2 fun i => ?_
  have h : AnalyticAt ℝ (fun I : Vec n => I i) Λ := analyticAt_pi_iff.mp analyticAt_id i
  have hm : D.m i ^ 2 * (D.G * D.m0) ≠ 0 := by
    have := D.hm i; have := D.hG; have := D.hm0; positivity
  exact (h.pow 2).div analyticAt_const hm

theorem axis_action (D : Data n) {a : Vec n} (ha : a ∈ axes n) : axis D (action D a) = a := by
  funext i
  exact action_sq_div D ha i

theorem action_axis (D : Data n) {Λ : Vec n} (hΛ : ∀ i, 0 < Λ i) :
    action D (axis D Λ) = Λ := by
  funext i
  have := D.hG; have := D.hm0; have := D.hm i; have := hΛ i
  have h0 : 0 < D.G * D.m0 := by positivity
  have h1 : D.G * D.m0 * (Λ i ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) = (Λ i / D.m i) ^ 2 := by
    field_simp
  unfold action axis
  rw [h1, Real.sqrt_sq (by positivity)]
  field_simp

theorem axis_pos (D : Data n) {Λ : Vec n} (hΛ : ∀ i, 0 < Λ i) (i : Fin n) : 0 < axis D Λ i := by
  have := D.hG; have := D.hm0; have := D.hm i; have := hΛ i
  unfold axis; positivity

theorem continuous_axis (D : Data n) : Continuous (axis D) := by
  refine continuous_pi fun i => ?_
  unfold axis
  fun_prop

theorem eventually_mem_axes {a : Vec n} (ha : a ∈ axes n) : ∀ᶠ b in 𝓝 a, b ∈ axes n := by
  have h1 : ∀ᶠ b in 𝓝 a, ∀ i, 0 < b i :=
    Filter.eventually_all.2 fun i =>
      (continuous_apply i).continuousAt.eventually (lt_mem_nhds (ha.1 i))
  have h2 : ∀ᶠ b in 𝓝 a, ∀ i j : Fin n, i < j → b i < b j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => by
      by_cases hij : i < j
      · have := ((continuous_apply i).continuousAt (x := a)).eventually_lt
          (continuous_apply j).continuousAt (ha.2 hij)
        filter_upwards [this] with b hb _ using hb
      · exact Filter.Eventually.of_forall fun b h => absurd h hij
  filter_upwards [h1, h2] with b hb1 hb2
  exact ⟨hb1, fun i j hij => hb2 i j hij⟩

/-- `axis D Λ` lies in `axes n` for `Λ` near `action D a`. -/
theorem eventually_axis_mem_axes (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∀ᶠ Λ in 𝓝 (action D a), axis D Λ ∈ axes n := by
  have h := (continuous_axis D).continuousAt (x := action D a)
  have hm : axes n ∈ 𝓝 (axis D (action D a)) := by
    rw [axis_action D ha]; exact eventually_mem_axes ha
  exact h.preimage_mem_nhds hm

theorem analyticAt_constantTerm (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    AnalyticAt ℝ (constantTerm D) a := by
  have hev : ∀ p : Fin n, AnalyticAt ℝ (fun b : Vec n => b p) a := fun p =>
    analyticAt_pi_iff.mp analyticAt_id p
  unfold constantTerm
  refine (Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j hj => ?_).neg
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have hr0 : 0 < a i / a j := div_pos (ha.1 i) (ha.1 j)
  have hr1 : a i / a j < 1 := (div_lt_one (ha.1 j)).2 (ha.2 hij)
  have hl : AnalyticAt ℝ (fun b : Vec n => laplace_def (1 / 2) 0 (b i / b j)) a :=
    AnalyticAt.comp (g := laplace_def (1 / 2) 0) (f := fun b : Vec n => b i / b j)
      (analyticOnNhd_laplace_def (by norm_num : (0 : ℝ) < 1 / 2) 0 _ ⟨hr0, hr1⟩)
      ((hev i).div (hev j) (ha.1 j).ne')
  exact (analyticAt_const.div (hev j) (ha.1 j).ne').mul hl

theorem analyticAt_quad (M : Mat n) (x₀ : Vec n) :
    AnalyticAt ℝ (fun p : Mat n × Vec n => quad p.1 p.2) (M, x₀) := by
  unfold quad
  refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => ?_
  have hx : ∀ k, AnalyticAt ℝ (fun p : Mat n × Vec n => p.2 k) (M, x₀) := fun k =>
    ((analyticAt_pi_iff.mp analyticAt_id k).comp analyticAt_snd)
  have hMi : AnalyticAt ℝ (fun M : Mat n => M i) M := analyticAt_pi_iff.mp analyticAt_id i
  have hMij : AnalyticAt ℝ (fun M : Mat n => M i j) M := analyticAt_pi_iff.mp hMi j
  have hM : AnalyticAt ℝ (fun p : Mat n × Vec n => p.1 i j) (M, x₀) :=
    hMij.comp_of_eq analyticAt_fst rfl
  exact ((hx i).mul hM).mul (hx j)

end SecularForm
end KAM.Planetary
end
