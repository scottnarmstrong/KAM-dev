/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Cauchy
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Uniform limits of holomorphic maps

Blueprint-W `bpW:w1:uniform-limit` (package W1-ANALYTIC). This is source-faithful infrastructure
used by several nodes; the dependency graph is still being built.

A uniform limit `g` of holomorphic maps `f k` on an open set `U` of a complex normed space, with
values in a complex Banach space, is holomorphic and `D (f k) → D g` uniformly on every ball
`B(w, δ)` with `B(w, 2δ) ⊆ U` (`KAM.Wave.holomorphic_of_tendstoUniformlyOn`). If the `f k` take
values in a closed set at the points of `S`, so does `g` (`KAM.Wave.mem_of_tendstoUniformlyOn`; in
the blueprint the closed set is the real subspace `ι ℓ²_ℝ`). The quantitative bound is the
Cauchy estimate for `g` itself (`KAM.Wave.norm_fderiv_le_div_of_tendstoUniformlyOn`).
-/

@[expose] public section

open Metric Set Filter Topology

namespace KAM.Wave

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The derivatives of a uniformly Cauchy sequence of holomorphic maps are uniformly Cauchy on
every ball with a margin of the same size. -/
theorem uniformCauchySeqOn_fderiv {f : ℕ → E → F} {U : Set E} (hU : IsOpen U)
    (hf : ∀ k, DifferentiableOn ℂ (f k) U) (hc : UniformCauchySeqOn f atTop U)
    {w : E} {δ : ℝ} (hδ : 0 < δ) (hw : ball w (2 * δ) ⊆ U) :
    UniformCauchySeqOn (fun k => fderiv ℂ (f k)) atTop (ball w δ) := by
  rw [Metric.uniformCauchySeqOn_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε * δ / 2) (by positivity)
  refine ⟨N, fun k hk l hl x hx => ?_⟩
  have hxδ : ball x δ ⊆ ball w (2 * δ) := fun y hy => by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    rw [mem_ball, dist_eq_norm] at hx
    have := norm_add_le (y - x) (x - w)
    simp only [sub_add_sub_cancel] at this
    linarith
  have hM : ∀ z ∈ ball x δ, ‖(f k - f l) z‖ ≤ ε * δ / 2 := fun z hz => by
    have := hN k hk l hl z (hw (hxδ hz))
    rw [dist_eq_norm] at this
    exact this.le
  have hd : DifferentiableOn ℂ (f k - f l) (ball x δ) :=
    ((hf k).sub (hf l)).mono (fun y hy => hw (hxδ hy))
  have key := norm_fderiv_le_div_of_ball hδ (by positivity) hd hM
  have hdk : DifferentiableAt ℂ (f k) x := (hf k).differentiableAt (hU.mem_nhds (hw (hxδ (mem_ball_self hδ))))
  have hdl : DifferentiableAt ℂ (f l) x := (hf l).differentiableAt (hU.mem_nhds (hw (hxδ (mem_ball_self hδ))))
  rw [fderiv_sub hdk hdl, dist_eq_norm] at *
  refine lt_of_le_of_lt key ?_
  rw [show ε * δ / 2 / δ = ε / 2 by field_simp]
  linarith


variable [CompleteSpace F]

/-- Blueprint `bpW:w1:uniform-limit` (i), qualitative: a uniform limit of holomorphic maps on an
open set is holomorphic, and the derivatives converge uniformly on every ball `B(w, δ)` with
`B(w, 2δ) ⊆ U`. No boundedness of the limit is assumed. -/
theorem holomorphic_of_tendstoUniformlyOn {f : ℕ → E → F} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ∀ k, DifferentiableOn ℂ (f k) U)
    (hg : TendstoUniformlyOn f g atTop U) :
    DifferentiableOn ℂ g U ∧ ∀ {w : E} {δ : ℝ}, 0 < δ → ball w (2 * δ) ⊆ U →
      TendstoUniformlyOn (fun k => fderiv ℂ (f k)) (fderiv ℂ g) atTop (ball w δ) := by
  have local_claim : ∀ {w : E} {δ : ℝ}, 0 < δ → ball w (2 * δ) ⊆ U →
      ∃ g' : E → E →L[ℂ] F, (∀ x ∈ ball w δ, HasFDerivAt g (g' x) x) ∧
        TendstoUniformlyOn (fun k => fderiv ℂ (f k)) g' atTop (ball w δ) := by
    intro w δ hδ hw
    have hcd := uniformCauchySeqOn_fderiv hU hf hg.uniformCauchySeqOn hδ hw
    have hlim : ∀ x ∈ ball w δ, ∃ y, Tendsto (fun k => fderiv ℂ (f k) x) atTop (𝓝 y) :=
      fun x hx => cauchySeq_tendsto_of_complete (hcd.cauchySeq hx)
    choose! g' hg' using hlim
    have htu : TendstoUniformlyOn (fun k => fderiv ℂ (f k)) g' atTop (ball w δ) :=
      hcd.tendstoUniformlyOn_of_tendsto hg'
    refine ⟨g', fun x hx => ?_, htu⟩
    exact hasFDerivAt_of_tendstoUniformlyOn isOpen_ball htu
      (fun n y hy => ((hf n).differentiableAt (hU.mem_nhds
        (hw (ball_subset_ball (by linarith) hy)))).hasFDerivAt)
      (fun y hy => hg.tendsto_at (hw (ball_subset_ball (by linarith) hy))) hx
  have hdiff : DifferentiableOn ℂ g U := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    have hδ : 0 < ε / 2 := by positivity
    have hsub : ball x (2 * (ε / 2)) ⊆ U := by
      have : 2 * (ε / 2) = ε := by ring
      rw [this]; exact hball
    obtain ⟨g', hg'1, -⟩ := local_claim hδ hsub
    exact (hg'1 x (mem_ball_self hδ)).differentiableAt.differentiableWithinAt
  refine ⟨hdiff, fun {w δ} hδ hw => ?_⟩
  obtain ⟨g', hg'1, htu⟩ := local_claim hδ hw
  exact htu.congr_right (fun x hx => ((hg'1 x hx).fderiv).symm)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Blueprint `bpW:w1:uniform-limit` (i), reality: if every `f k` takes values in a closed set `R`
at the points of `S ⊆ U`, so does the limit (in the blueprint `R` is `ι ℓ²_ℝ` and `S` the real
points). -/
theorem mem_of_tendstoUniformlyOn {f : ℕ → E → F} {g : E → F} {U : Set E}
    (hg : TendstoUniformlyOn f g atTop U) {R : Set F} (hR : IsClosed R) {S : Set E} (hS : S ⊆ U)
    (hfR : ∀ k, ∀ z ∈ S, f k z ∈ R) : ∀ z ∈ S, g z ∈ R := fun z hz =>
  hR.mem_of_tendsto (hg.tendsto_at (hS hz)) (Eventually.of_forall fun k => hfR k z hz)

/-- Blueprint `bpW:w1:uniform-limit` (ii), quantitative: a bound `‖g‖ ≤ M` on `U` gives
`‖D g (w)‖ ≤ M / δ` whenever `B(w, δ) ⊆ U`. -/
theorem norm_fderiv_le_div_of_tendstoUniformlyOn {f : ℕ → E → F} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ∀ k, DifferentiableOn ℂ (f k) U)
    (hg : TendstoUniformlyOn f g atTop U) {M : ℝ} (hM : 0 ≤ M) (hbd : ∀ z ∈ U, ‖g z‖ ≤ M)
    {w : E} {δ : ℝ} (hδ : 0 < δ) (hw : ball w δ ⊆ U) : ‖fderiv ℂ g w‖ ≤ M / δ :=
  norm_fderiv_le_div_of_ball_subset hδ hM (holomorphic_of_tendstoUniformlyOn hU hf hg).1 hbd hw

end KAM.Wave
