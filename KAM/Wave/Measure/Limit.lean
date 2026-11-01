/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Shells
public import KAM.Wave.Measure.Coords

/-!
# W7: the frequency limit (blueprint `bpW:w7:limit`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

If `Γ ⊆ ⋃_k R_k` and `‖ω_* - ω⁰‖_∞ ≤ e_k` on `Γ ∩ R_k` with `e_k → 0`, then `ν = ω_* / (2π)`
tends to `λ_J / (2π)` as `I → 0` in `Γ`, in the exact form of clause (2) of the frozen
`KAM.Wave.nlw2` (the Lean index `i : Fin 2` is the Dirichlet mode `i + 1`).
-/

@[expose] public noncomputable section

open Real MeasureTheory Set Filter Topology

namespace KAM.Wave

/-- **Frequency limit** (blueprint `bpW:w7:limit`). -/
theorem tendsto_frequency_limit (m : ℝ) (hm : 0 < m) {q t0 : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ht : 0 < t0) {Γ : Set (Fin 2 → ℝ)} (hΓ : ∀ I ∈ Γ, ∃ k, I ∈ shellSet q t0 k)
    (ωs : (Fin 2 → ℝ) → Fin 2 → ℝ) (e : ℕ → ℝ)
    (he : ∀ k, ∀ I ∈ Γ, I ∈ shellSet q t0 k → ‖ωs I - omegaTan m hm I‖ ≤ e k)
    (hek : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun I : Fin 2 → ℝ => fun i => ωs I i / (2 * π)) (𝓝[Γ] 0)
      (𝓝 fun i : Fin 2 => lam m hm (i : ℕ).succPNat / (2 * π)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hpi := Real.pi_pos
  have hNA := measNA_pos m hm
  obtain ⟨k0, hk0⟩ := (hek.eventually (gt_mem_nhds (show (0 : ℝ) < π * ε by
      positivity))).exists_forall_of_atTop
  refine ⟨min (shellT q t0 (k0 + 1)) (π * ε / measNA m hm), lt_min (shellT_pos hq ht _)
    (by positivity), fun I hI hdist => ?_⟩
  rw [dist_zero_right] at hdist
  have hIt : ‖I‖ < shellT q t0 (k0 + 1) := lt_of_lt_of_le hdist (min_le_left _ _)
  have hIN : ‖I‖ < π * ε / measNA m hm := lt_of_lt_of_le hdist (min_le_right _ _)
  obtain ⟨k, hk⟩ := hΓ I hI
  have hkk : k0 < k := by
    by_contra hcon
    push Not at hcon
    have h1 := shellSet_norm_ge hk
    have h2 : shellT q t0 (k0 + 1) ≤ shellT q t0 (k + 1) :=
      (shellT_antitone hq hq1 ht).antitone (by omega)
    linarith
  have hek' := hk0 k hkk.le
  have h1 := he k I hI hk
  have h2 := norm_omegaTan_sub_le m hm I 0
  have e0 : omegaTan m hm 0 = fun i => lamTan m hm i := by funext i; simp [omegaTan]
  rw [e0, sub_zero] at h2
  have h3 : measNA m hm * ‖I‖ < π * ε := by
    have := mul_lt_mul_of_pos_left hIN hNA
    rwa [mul_div_cancel₀ _ hNA.ne'] at this
  have h4 : ‖ωs I - fun i => lamTan m hm i‖ < 2 * (π * ε) := by
    have : ωs I - (fun i => lamTan m hm i) =
        (ωs I - omegaTan m hm I) + (omegaTan m hm I - fun i => lamTan m hm i) := by abel
    rw [this]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    linarith
  rw [dist_pi_lt_iff hε]
  intro i
  rw [Real.dist_eq]
  have h5 : |ωs I i - lamTan m hm i| ≤ ‖ωs I - fun i => lamTan m hm i‖ := by
    have := norm_le_pi_norm (ωs I - fun i => lamTan m hm i) i
    simpa using this
  have e1 : lam m hm (i : ℕ).succPNat = lamTan m hm i := rfl
  rw [e1, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * π), div_lt_iff₀ (by positivity)]
  nlinarith

end KAM.Wave

end
