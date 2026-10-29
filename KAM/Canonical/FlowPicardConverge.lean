/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.FlowPicard
public import KAM.ODE.Lipschitz

/-!
# Convergence of the Picard iterates to the canonical flow

Helper module of `KAM.Canonical.FlowRegular` (blueprint-N Part 5, node `bpN:p5:flow`
(b)). For `z₀ ∈ Ω^{1/2}` there are `η > 0` and `Λ ≥ 0` such that, for every `z` with
`ν(z - z₀) < η`, the Picard iterates `y_k` satisfy

  `ν(y_k(t, z) - X^t(z)) ≤ ε Λ^k |t|^{k+1} / (k+1)!`   for `|t| ≤ 1`

(`KAM.Canonical.picard_flow_estimate`). The comparison is made with the flow of `flow_a` directly
(its displacement bound starts the induction and its integral equation
`KAM.Canonical.flow_integral_eq` drives it), so no limit has to be identified afterwards.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped Interval

namespace KAM.Canonical

section Converge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The flow satisfies the integral equation `X^t(z) = z + ∫₀ᵗ F(X^τ(z)) dτ` on `[-1, 1]`. -/
theorem flow_integral_eq {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε)
    {z : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    flow F Ω t z = z + ∫ τ in (0 : ℝ)..t, F (flow F Ω τ z) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨h0, hsol, -, -⟩ := flow_a h hz
  have h00 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hsub : uIcc (0 : ℝ) t ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h00 ht
  have hcont : ContinuousOn (fun τ => F (flow F Ω τ z)) (uIcc (0 : ℝ) t) := by
    refine h.differentiableOn.continuousOn.comp (hsol.continuousOn.mono hsub) fun τ hτ => ?_
    exact (hsol τ (hsub hτ)).1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ => flow F Ω τ z) (f' := fun τ => F (flow F Ω τ z))
    (fun τ hτ => (hsol τ (hsub hτ)).2) (hcont.intervalIntegrable)
  rw [this, h0]
  abel

/-- Uniform convergence from a null sequence of uniform bounds. -/
theorem tendstoUniformlyOn_of_bound {α β : Type*} [PseudoMetricSpace β] {f : ℕ → α → β}
    {g : α → β} {s : Set α} {δ : ℕ → ℝ} (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (h : ∀ k, ∀ x ∈ s, dist (f k x) (g x) ≤ δ k) :
    TendstoUniformlyOn f g Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hδ.eventually (gt_mem_nhds hε)] with k hk x hx
  rw [dist_comm]
  exact (h k x hx).trans_lt hk

/-- The local estimate for the Picard iterates against the flow. -/
theorem picard_flow_estimate {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z₀ : E} (hz₀ : z₀ ∈ gaugeInterior W Ω (1 / 2)) :
    ∃ η Λ : ℝ, 0 < η ∧ 0 ≤ Λ ∧
      (∀ z, ‖W (z - z₀)‖ < η → z ∈ gaugeInterior W Ω (1 / 2)) ∧
      ∀ z, ‖W (z - z₀)‖ < η → ∀ k : ℕ, ∀ t ∈ Icc (-1 : ℝ) 1,
        ‖W (picard F k t z - flow F Ω t z)‖ ≤
          ε * Λ ^ k * |t| ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨η, hη, hz₀η⟩ := exists_gaugeInterior_gt' h.isOpen W hz₀
  have hKc : IsCompact {w : E | ‖W (w - z₀)‖ ≤ 1 / 2 + η} := isCompact_gaugeBall' W z₀ _
  have hKΩ : {w : E | ‖W (w - z₀)‖ ≤ 1 / 2 + η} ⊆ Ω := fun w hw => hz₀η w hw
  have hC1 : ContDiffOn ℝ 1 F Ω :=
    ((KAM.contDiffOn_infty_of_differentiableOn h.isOpen h.differentiableOn).restrict_scalars
      ℝ).of_le (by exact_mod_cast le_top)
  obtain ⟨-, L, hL⟩ := KAM.ODE.gen_lip h.isOpen hC1 hKc hKΩ
  -- the gauge Lipschitz constant on the ball
  have hlip : ∀ a ∈ {w : E | ‖W (w - z₀)‖ ≤ 1 / 2 + η}, ∀ b ∈ {w : E | ‖W (w - z₀)‖ ≤ 1 / 2 + η},
      ‖W (F a - F b)‖ ≤ (‖W.toContinuousLinearMap‖ * (L : ℝ) * ‖W.symm.toContinuousLinearMap‖) *
        ‖W (a - b)‖ := by
    intro a ha b hb
    have h1 : ‖W (F a - F b)‖ ≤ ‖W.toContinuousLinearMap‖ * ‖F a - F b‖ :=
      W.toContinuousLinearMap.le_opNorm _
    have h2 : ‖F a - F b‖ ≤ (L : ℝ) * ‖a - b‖ := by
      have := hL.dist_le_mul a ha b hb
      simpa [dist_eq_norm] using this
    have h3 : ‖a - b‖ ≤ ‖W.symm.toContinuousLinearMap‖ * ‖W (a - b)‖ := by
      have := W.symm.toContinuousLinearMap.le_opNorm (W (a - b))
      simpa using this
    calc ‖W (F a - F b)‖ ≤ ‖W.toContinuousLinearMap‖ * ((L : ℝ) * ‖a - b‖) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ ≤ ‖W.toContinuousLinearMap‖ * ((L : ℝ) * (‖W.symm.toContinuousLinearMap‖ * ‖W (a - b)‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 L.coe_nonneg) (norm_nonneg _)
      _ = _ := by ring
  have hKz : ∀ z : E, ‖W (z - z₀)‖ < η → ∀ w : E, ‖W (w - z)‖ ≤ 1 / 2 →
      ‖W (w - z₀)‖ ≤ 1 / 2 + η := by
    intro z hz w hw
    have : W (w - z₀) = W (w - z) + W (z - z₀) := by rw [← map_add]; congr 1; abel
    rw [this]
    exact (norm_add_le _ _).trans (by linarith)
  refine ⟨η, ‖W.toContinuousLinearMap‖ * (L : ℝ) * ‖W.symm.toContinuousLinearMap‖, hη,
    by positivity, ?_, ?_⟩
  · intro z hz w hw
    exact hKΩ (hKz z hz w hw)
  · intro z hz k
    have hzU : z ∈ gaugeInterior W Ω (1 / 2) := fun w hw => hKΩ (hKz z hz w hw)
    obtain ⟨-, hsol, -, hdisp⟩ := flow_a h hzU
    have hΛ : (0 : ℝ) ≤ ‖W.toContinuousLinearMap‖ * (L : ℝ) * ‖W.symm.toContinuousLinearMap‖ := by
      positivity
    -- both curves stay in the compact ball
    have hflowK : ∀ τ ∈ Icc (-1 : ℝ) 1, flow F Ω τ z ∈ {w : E | ‖W (w - z₀)‖ ≤ 1 / 2 + η} :=
      fun τ hτ => hKz z hz _ ((hdisp τ hτ).trans (abs_mul_le_half h hτ))
    have hpicK : ∀ m : ℕ, ∀ τ ∈ Icc (-1 : ℝ) 1,
        picard F m τ z ∈ {w : E | ‖W (w - z₀)‖ ≤ 1 / 2 + η} :=
      fun m τ hτ => hKz z hz _ (((picard_regular h m).2 τ hτ z hzU).trans (abs_mul_le_half h hτ))
    induction k with
    | zero =>
      intro t ht
      have := hdisp t ht
      rw [← norm_neg, ← map_neg, neg_sub] at this
      simpa [picard_zero, mul_comm] using this
    | succ k ih =>
      intro t ht
      have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have hsub : uIcc (0 : ℝ) t ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0 ht
      have hint1 := intervalIntegrable_picard_field h k hzU ht
      have hint2 : IntervalIntegrable (fun τ => F (flow F Ω τ z)) volume 0 t := by
        refine ContinuousOn.intervalIntegrable ?_
        refine h.differentiableOn.continuousOn.comp (hsol.continuousOn.mono hsub) fun τ hτ => ?_
        exact (hsol τ (hsub hτ)).1
      have heq : picard F (k + 1) t z - flow F Ω t z =
          ∫ τ in (0 : ℝ)..t, (F (picard F k τ z) - F (flow F Ω τ z)) := by
        rw [intervalIntegral.integral_sub hint1 hint2, picard_succ, flow_integral_eq h hzU ht]
        abel
      rw [heq]
      have hb : ∀ τ ∈ Ι (0 : ℝ) t,
          ‖W (F (picard F k τ z) - F (flow F Ω τ z))‖ ≤
            (ε * (‖W.toContinuousLinearMap‖ * (L : ℝ) * ‖W.symm.toContinuousLinearMap‖) ^ (k + 1) /
              (((k + 1).factorial : ℕ) : ℝ)) * |τ| ^ (k + 1) := by
        intro τ hτ
        have hτI : τ ∈ Icc (-1 : ℝ) 1 := hsub (uIoc_subset_uIcc hτ)
        have h1 := hlip _ (hpicK k τ hτI) _ (hflowK τ hτI)
        have h2 := ih τ hτI
        calc _ ≤ _ := h1
          _ ≤ (‖W.toContinuousLinearMap‖ * (L : ℝ) * ‖W.symm.toContinuousLinearMap‖) *
              (ε * (‖W.toContinuousLinearMap‖ * (L : ℝ) * ‖W.symm.toContinuousLinearMap‖) ^ k *
                |τ| ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 hΛ
          _ = _ := by ring
      have hbound := norm_gauge_intervalIntegral_le (W := W)
        (f := fun τ => F (picard F k τ z) - F (flow F Ω τ z))
        (hint1.sub hint2) hb
      refine hbound.trans (le_of_eq ?_)
      rw [Nat.factorial_succ (k + 1)]
      push_cast
      field_simp

end Converge

end KAM.Canonical
