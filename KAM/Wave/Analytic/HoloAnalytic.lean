/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Analytic
public import KAM.Wave.Analytic.Separable
public import KAM.Wave.Analytic.DegreeSeries

/-!
# Holomorphic maps of finitely many variables with Banach values are analytic

Blueprint-W `bpW:w1:holo-analytic-fd` (package W1-ANALYTIC). This is source-faithful infrastructure
used by several nodes; the dependency graph is still being built.

Track K proves the analogous statement for second-countable targets
(`KAM.analyticOnNhd_of_differentiableOn`, `KAM.exists_powerSeries_coeff`). Steps `hacoef`: via the
separable reduction `KAM.Wave.exists_separable_lift` the coefficient theorem holds for an arbitrary
complex Banach space (`KAM.Wave.exists_powerSeries_coeff_banach`), hence so does analyticity
(`KAM.Wave.analyticOnNhd_of_differentiableOn_banach`; this covers `n = 0` too). Steps `hamargin`,
`hagroup`: the quantitative statement for `n ≥ 1` is
`KAM.Wave.holomorphic_fd_power_series`, with the degree-grouped series `KAM.Wave.degreeSeries`.
-/

@[expose] public section

open Metric Set Filter Topology

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Blueprint `stepW:w1:hacoef`: the multi-index power series coefficients of a holomorphic map
with values in an arbitrary complex Banach space. -/
theorem exists_powerSeries_coeff_banach {m : ℕ} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    {f : (Fin m → ℂ) → F} (hf : DifferentiableOn ℂ f U) {z₀ : Fin m → ℂ} {r : ℝ} (hr : 0 < r)
    (hcl : closedBall z₀ r ⊆ U) :
    ∃ c : (Fin m → ℕ) → F,
      (∀ A : ℝ, (∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ A) → ∀ α, ‖c α‖ ≤ A / r ^ (∑ j, α j)) ∧
      ∀ z ∈ ball z₀ r,
        HasSum (fun α : Fin m → ℕ => (∏ j, (z j - z₀ j) ^ α j) • c α) (f z) := by
  obtain ⟨F₀, hcl₀, hsc, f₀, hd, hf₀⟩ := exists_separable_lift hU hf
  have : CompleteSpace F₀ := hcl₀.completeSpace_coe
  obtain ⟨c, h1, h2⟩ := KAM.exists_powerSeries_coeff m hU hd hr hcl
  refine ⟨fun α => (c α : F), fun A hA α => ?_, fun z hz => ?_⟩
  · have := h1 A (fun z hz => by
      have e : ‖f₀ z‖ = ‖f z‖ := by
        rw [← hf₀ z (hcl hz)]; rfl
      rw [e]; exact hA z hz) α
    simpa using this
  · have := F₀.subtypeL.hasSum (h2 z hz)
    simpa [hf₀ z (hcl (ball_subset_closedBall hz))] using this

/-- Blueprint `bpW:w1:holo-analytic-fd`, first assertion: a holomorphic map on an open subset of
`ℂⁿ` with values in a complex Banach space is `ℂ`-analytic. (For `n = 0` this is included.) -/
theorem analyticOnNhd_of_differentiableOn_banach {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  obtain ⟨F₀, hcl₀, hsc, f₀, hd, hf₀⟩ := exists_separable_lift hU hf
  have : CompleteSpace F₀ := hcl₀.completeSpace_coe
  intro z hz
  have h1 : AnalyticAt ℂ (fun x => (f₀ x : F)) z :=
    (F₀.subtypeL.analyticAt _).comp (KAM.analyticOnNhd_of_differentiableOn hU hd z hz)
  refine h1.congr ?_
  filter_upwards [hU.mem_nhds hz] with x hx
  exact hf₀ x hx

end KAM.Wave
