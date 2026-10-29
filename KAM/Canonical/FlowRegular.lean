/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.FlowPicardConverge
public import KAM.Weighted.Parametric

/-!
# The canonical flow: regularity and the variational equation

Blueprint-N Part 5, node `bpN:p5:flow`, part (b).

* `KAM.Canonical.flow_b`: the flow is jointly continuous on `[-1, 1] × Ω^{1/2}`, holomorphic in the
  initial point, stays in `Ω`, has jointly continuous derivative, and satisfies the variational
  equation `DX^t(z) = 1 + ∫₀ᵗ DF(X^τ z) DX^τ(z) dτ`.

Proof. The Picard iterates `y_k` of `FlowPicard` are holomorphic in `z` with continuous derivative
(by differentiation under the integral sign, `FlowRegularIntegral`). Near `z₀` they converge to the
flow uniformly in `(t, z)` at the rate `ε Λ^k / k!` (`FlowPicardConverge`). Hence the flow is a
uniform limit of holomorphic maps, so it is holomorphic (`KAM.Weighted.uniform_limit_holomorphic`),
and the Cauchy estimate `KAM.Weighted.general_cauchy` for `y_k - X^t` gives uniform convergence of
the derivatives, uniformly in `t`. The variational equation is then the derivative formula for the
integral equation `X^t(z) = z + ∫₀ᵗ F(X^τ z) dτ`, whose integrand has the same regularity.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Canonical

section FlowRegular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- `ParamHyp` is a local property in the space variable. -/
theorem ParamHyp.of_local {U : Set E} {y : ℝ → E → E}
    (hloc : ∀ z₀ ∈ U, ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ParamHyp V y) :
    ParamHyp U y where
  cont := by
    refine continuousOn_of_locally_continuousOn fun p hp => ?_
    obtain ⟨V, hV, hzV, -, hy⟩ := hloc p.2 hp.2
    exact ⟨univ ×ˢ V, isOpen_univ.prod hV, ⟨mem_univ _, hzV⟩,
      hy.cont.mono fun q hq => ⟨hq.1.1, hq.2.2⟩⟩
  diff := fun t ht z hz => by
    obtain ⟨V, hV, hzV, -, hy⟩ := hloc z hz
    exact ((hy.diff t ht z hzV).differentiableAt (hV.mem_nhds hzV)).differentiableWithinAt
  contD := by
    refine continuousOn_of_locally_continuousOn fun p hp => ?_
    obtain ⟨V, hV, hzV, -, hy⟩ := hloc p.2 hp.2
    exact ⟨univ ×ˢ V, isOpen_univ.prod hV, ⟨mem_univ _, hzV⟩,
      hy.contD.mono fun q hq => ⟨hq.1.1, hq.2.2⟩⟩

omit [FiniteDimensional ℂ E] in
/-- The elementary bound turning the factorial estimate into a null sequence. -/
theorem picard_bound_le {ε Λ t : ℝ} (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ) (ht : t ∈ Icc (-1 : ℝ) 1)
    (k : ℕ) :
    ε * Λ ^ k * |t| ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ) ≤
      ε * (Λ ^ k / (k.factorial : ℝ)) := by
  have h1 : |t| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (abs_le.2 ⟨ht.1, ht.2⟩)
  have h2 : (k.factorial : ℝ) ≤ (((k + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have h3 : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos k)
  have h4 : 0 ≤ ε * Λ ^ k := mul_nonneg hε (pow_nonneg hΛ k)
  calc ε * Λ ^ k * |t| ^ (k + 1) / (((k + 1).factorial : ℕ) : ℝ)
      ≤ ε * Λ ^ k * 1 / (((k + 1).factorial : ℕ) : ℝ) := by gcongr
    _ ≤ ε * Λ ^ k * 1 / (k.factorial : ℝ) := div_le_div_of_nonneg_left (by positivity) h3 h2
    _ = ε * (Λ ^ k / (k.factorial : ℝ)) := by ring

/-- Local regularity of the flow: near `z₀ ∈ Ω^{1/2}` the flow is a `ParamHyp` family. -/
theorem flow_paramHyp_local {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z₀ : E} (hz₀ : z₀ ∈ gaugeInterior W Ω (1 / 2)) :
    ∃ V : Set E, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ gaugeInterior W Ω (1 / 2) ∧ ParamHyp V (flow F Ω) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨η, Λ, hη, hΛ, hVU, hest⟩ := picard_flow_estimate h hz₀
  obtain ⟨cW, hcW⟩ : ∃ c : ℝ, c = ‖W.toContinuousLinearMap‖ := ⟨_, rfl⟩
  obtain ⟨cWi, hcWi⟩ : ∃ c : ℝ, c = ‖W.symm.toContinuousLinearMap‖ := ⟨_, rfl⟩
  have hcW0 : 0 ≤ cW := hcW ▸ norm_nonneg _
  have hcWi0 : 0 ≤ cWi := hcWi ▸ norm_nonneg _
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = η / (2 * (cW + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hcWr : cW * r ≤ η / 2 := by
    rw [hr, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun k => cWi * (ε * (Λ ^ k / (k.factorial : ℝ))) :=
    ⟨_, rfl⟩
  have hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have := ((FloorSemiring.tendsto_pow_div_factorial_atTop Λ).const_mul ε).const_mul cWi
    simpa [hδ] using this
  -- the open sets
  let V : Set E := {z | ‖W (z - z₀)‖ < η}
  let V' : Set E := {z | ‖W (z - z₀)‖ < η / 2}
  have hVo : IsOpen V :=
    isOpen_lt (continuous_norm.comp (W.continuous.comp (continuous_id.sub continuous_const)))
      continuous_const
  have hV'o : IsOpen V' :=
    isOpen_lt (continuous_norm.comp (W.continuous.comp (continuous_id.sub continuous_const)))
      continuous_const
  have hz₀V' : z₀ ∈ V' := by simp [V', hη]
  have hV'V : V' ⊆ V := fun z hz => by
    have h2 : ‖W (z - z₀)‖ < η / 2 := hz
    show ‖W (z - z₀)‖ < η
    linarith
  have hVU₀ : V ⊆ gaugeInterior W Ω (1 / 2) := fun z hz => hVU z hz
  have hball : ∀ z ∈ V', ball z r ⊆ V := by
    intro z hz w hw
    have h1 : ‖W (w - z)‖ ≤ cW * ‖w - z‖ := by
      have := W.toContinuousLinearMap.le_opNorm (w - z)
      simpa [hcW] using this
    have h2 : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
    have h3 : ‖W (w - z)‖ ≤ η / 2 := h1.trans ((mul_le_mul_of_nonneg_left h2.le hcW0).trans hcWr)
    have : W (w - z₀) = W (w - z) + W (z - z₀) := by rw [← map_add]; congr 1; abel
    show ‖W (w - z₀)‖ < η
    rw [this]
    exact (norm_add_le _ _).trans_lt (by have : ‖W (z - z₀)‖ < η / 2 := hz; linarith)
  -- the uniform bound
  have hbound : ∀ k : ℕ, ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ V,
      ‖picard F k t z - flow F Ω t z‖ ≤ δ k := by
    intro k t ht z hz
    have h1 := hest z hz k t ht
    have h2 : ‖picard F k t z - flow F Ω t z‖ ≤ cWi * ‖W (picard F k t z - flow F Ω t z)‖ := by
      have := W.symm.toContinuousLinearMap.le_opNorm (W (picard F k t z - flow F Ω t z))
      simpa [hcWi] using this
    rw [hδ]
    exact h2.trans (mul_le_mul_of_nonneg_left (h1.trans (picard_bound_le h.eps_nonneg hΛ ht k))
      hcWi0)
  have hreg := fun k => (picard_regular h k).1
  have hU := isOpen_gaugeInterior h.isOpen W (1 / 2)
  -- holomorphy of the flow on `V`
  have hdiff : ∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ (flow F Ω t) V := by
    intro t ht
    refine (KAM.Weighted.uniform_limit_holomorphic hVo
      (K := fun j => picard F j t) (K₀ := flow F Ω t)
      (fun j => ((hreg j).diff t ht).mono hVU₀) ?_).1
    exact tendstoUniformlyOn_of_bound hδ0 fun k z hz => by
      rw [dist_eq_norm]; exact hbound k t ht z hz
  refine ⟨V', hV'o, hz₀V', hV'V.trans hVU₀, ?_, ?_, ?_⟩
  · -- joint continuity
    refine TendstoUniformlyOn.continuousOn (F := fun k (p : ℝ × E) => picard F k p.1 p.2)
      (tendstoUniformlyOn_of_bound hδ0 fun k p hp => ?_)
      (Filter.Eventually.of_forall fun k => (hreg k).cont.mono
        (prod_mono subset_rfl (hV'V.trans hVU₀))).frequently
    rw [dist_eq_norm]; exact hbound k p.1 hp.1 p.2 (hV'V hp.2)
  · exact fun t ht => (hdiff t ht).mono hV'V
  · -- continuity of the derivative
    have hcauchy : ∀ k : ℕ, ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ V',
        dist (fderiv ℂ (picard F k t) z) (fderiv ℂ (flow F Ω t) z) ≤ δ k / r := by
      intro k t ht z hz
      have hzV : z ∈ V := hV'V hz
      have hG : DifferentiableOn ℂ (fun w => picard F k t w - flow F Ω t w) (ball z r) :=
        (((hreg k).diff t ht).mono hVU₀ |>.mono (hball z hz)).sub ((hdiff t ht).mono (hball z hz))
      have hM : ∀ a ∈ ball z r, ‖picard F k t a - flow F Ω t a‖ ≤ δ k :=
        fun a ha => hbound k t ht a (hball z hz ha)
      have hc := KAM.Weighted.general_cauchy hr0 hG hM
      have hfd : fderiv ℂ (fun w => picard F k t w - flow F Ω t w) z =
          fderiv ℂ (picard F k t) z - fderiv ℂ (flow F Ω t) z :=
        fderiv_sub (((hreg k).diff t ht).differentiableAt (hU.mem_nhds (hVU₀ hzV)))
          ((hdiff t ht).differentiableAt (hVo.mem_nhds hzV))
      rw [dist_eq_norm, ← hfd]
      exact hc
    have hδr : Filter.Tendsto (fun k => δ k / r) Filter.atTop (nhds 0) := by
      simpa using hδ0.div_const r
    refine TendstoUniformlyOn.continuousOn
      (F := fun k (p : ℝ × E) => fderiv ℂ (picard F k p.1) p.2)
      (tendstoUniformlyOn_of_bound hδr fun k p hp => hcauchy k p.1 hp.1 p.2 hp.2)
      (Filter.Eventually.of_forall fun k => (hreg k).contD.mono
        (prod_mono subset_rfl (hV'V.trans hVU₀))).frequently

/-- The flow is a `ParamHyp` family on `Ω^{1/2}`. -/
theorem flow_paramHyp {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε) :
    ParamHyp (gaugeInterior W Ω (1 / 2)) (flow F Ω) :=
  ParamHyp.of_local fun _ hz₀ => flow_paramHyp_local h hz₀

/-- (b) regularity, and the variational integral equation `Y(t) = 1 + ∫₀ᵗ DF(X^τ z) Y(τ) dτ`. -/
theorem flow_b {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ} (h : SmallField W Ω F ε) :
    ContinuousOn (fun p : ℝ × E => flow F Ω p.1 p.2) (Icc (-1) 1 ×ˢ gaugeInterior W Ω (1 / 2)) ∧
    (∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ (flow F Ω t) (gaugeInterior W Ω (1 / 2))) ∧
    (∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ gaugeInterior W Ω (1 / 2), flow F Ω t z ∈ Ω) ∧
    ContinuousOn (fun p : ℝ × E => fderiv ℂ (flow F Ω p.1) p.2)
      (Icc (-1) 1 ×ˢ gaugeInterior W Ω (1 / 2)) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ gaugeInterior W Ω (1 / 2),
      fderiv ℂ (flow F Ω t) z = ContinuousLinearMap.id ℂ E +
        ∫ τ in (0 : ℝ)..t, (fderiv ℂ F (flow F Ω τ z)).comp (fderiv ℂ (flow F Ω τ) z) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hU := isOpen_gaugeInterior h.isOpen W (1 / 2)
  have hp := flow_paramHyp h
  have hmap : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ z ∈ gaugeInterior W Ω (1 / 2), flow F Ω t z ∈ Ω := by
    intro t ht z hz
    obtain ⟨-, -, -, hdisp⟩ := flow_a h hz
    exact mem_of_displacement h hz ht (hdisp t ht)
  refine ⟨hp.cont, hp.diff, hmap, hp.contD, ?_⟩
  intro t ht z hz
  obtain ⟨hg, hder⟩ := ParamHyp.comp_field h hU hp hmap
  obtain ⟨-, hder2⟩ := hg.id_add hU
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hsub : uIcc (0 : ℝ) t ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0 ht
  have hev : flow F Ω t =ᶠ[nhds z] fun w => w + ∫ τ in (0 : ℝ)..t, F (flow F Ω τ w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact flow_integral_eq h hw ht
  rw [hev.fderiv_eq, hder2 t ht z hz]
  congr 1
  exact intervalIntegral.integral_congr fun τ hτ => hder τ (hsub hτ) z hz

end FlowRegular

end KAM.Canonical
