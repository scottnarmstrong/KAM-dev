/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Analytic
public import KAM.Wave.Analytic.Separable
public import KAM.Wave.Analytic.DegreeSeries
public import KAM.Wave.Analytic.Complexification

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


/-- The sum of a function over the multi-indices of degree `m` is a finite sum over the
antidiagonal. -/
theorem tsum_degree_fiber {n : ℕ} {G : Type*} [AddCommMonoid G] [TopologicalSpace G] [T2Space G]
    (g : (Fin n → ℕ) → G) (m : ℕ) :
    ∑' α : (fun α : Fin n → ℕ => ∑ i, α i) ⁻¹' {m}, g α =
      ∑ α ∈ Finset.Nat.antidiagonalTuple n m, g α := by
  have hset : (fun α : Fin n → ℕ => ∑ i, α i) ⁻¹' {m} =
      ((Finset.Nat.antidiagonalTuple n m : Finset (Fin n → ℕ)) : Set (Fin n → ℕ)) := by
    ext α
    simp [Finset.Nat.mem_antidiagonalTuple]
  rw [← Finset.tsum_subtype' (Finset.Nat.antidiagonalTuple n m) g]
  exact tsum_congr_set_coe g hset


/-- Polynomial-times-geometric summability: `∑_m #{|α| = m} t^m = (1 - t)^{-n}`. -/
theorem summable_card_mul_pow (n : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    Summable fun m : ℕ => ((Finset.Nat.antidiagonalTuple n m).card : ℝ) * t ^ m := by
  have h := (KAM.hasSum_pow_sum n h0 h1).tsum_fiberwise (fun α : Fin n → ℕ => ∑ i, α i)
  refine h.summable.congr fun m => ?_
  rw [tsum_degree_fiber (fun α : Fin n → ℕ => t ^ ∑ i, α i) m,
    Finset.sum_congr rfl (g := fun _ => t ^ m) (fun α hα => by
    rw [Finset.Nat.mem_antidiagonalTuple.mp hα])]
  simp

/-- Blueprint `bpW:w1:holo-analytic-fd` (quantitative, `n ≥ 1`; steps `stepW:w1:hamargin`,
`stepW:w1:hacoef`, `stepW:w1:hagroup`). If `f` is holomorphic on `U ⊆ ℂⁿ` with values in a complex
Banach space and `closedBall z₀ r ⊆ U`, there are `r₁ > r` and `M₁ ≥ 0` with
`closedBall z₀ r₁ ⊆ U`, `‖f‖ ≤ M₁` there, and coefficients `c α` with `‖c α‖ ≤ M₁ r₁^{-|α|}` whose
absolutely convergent multi-index series sums to `f` on `ball z₀ r₁`; grouped by degree it is the
formal multilinear series `p = degreeSeries c`, with `‖p m‖ ≤ binom (m+n-1, n-1) M₁ r₁^{-m}`, and
`HasFPowerSeriesOnBall f p z₀ r₁`. -/
theorem holomorphic_fd_power_series {n : ℕ} (hn : 1 ≤ n) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f U) {z₀ : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hcl : closedBall z₀ r ⊆ U) :
    ∃ r₁ : ℝ, r < r₁ ∧ ∃ M₁ : ℝ, 0 ≤ M₁ ∧ closedBall z₀ r₁ ⊆ U ∧
      (∀ z ∈ closedBall z₀ r₁, ‖f z‖ ≤ M₁) ∧
      ∃ c : (Fin n → ℕ) → F, (∀ α, ‖c α‖ ≤ M₁ / r₁ ^ (∑ j, α j)) ∧
        (∀ z ∈ ball z₀ r₁,
          Summable (fun α : Fin n → ℕ => ‖(∏ j, (z j - z₀ j) ^ α j) • c α‖) ∧
          HasSum (fun α : Fin n → ℕ => (∏ j, (z j - z₀ j) ^ α j) • c α) (f z)) ∧
        ∃ p : FormalMultilinearSeries ℂ (Fin n → ℂ) F,
          (∀ m : ℕ, ‖p m‖ ≤ ((m + n - 1).choose (n - 1) : ℝ) * (M₁ / r₁ ^ m)) ∧
          (∀ (m : ℕ) (h : Fin n → ℂ), p m (fun _ => h) =
            ∑ α ∈ Finset.Nat.antidiagonalTuple n m, (∏ i, h i ^ α i) • c α) ∧
          HasFPowerSeriesOnBall f p z₀ (ENNReal.ofReal r₁) := by
  obtain ⟨⟨r₂, hr₂, hcl₂⟩, -⟩ := KAM.han_margin hU hf hr hcl
  obtain ⟨r₁, hr₁def⟩ : ∃ r₁ : ℝ, r₁ = (r + r₂) / 2 := ⟨_, rfl⟩
  have hr₁ : r < r₁ := by rw [hr₁def]; linarith
  have hr₁₂ : r₁ < r₂ := by rw [hr₁def]; linarith
  have hr₁0 : 0 < r₁ := hr.trans hr₁
  have hcl₁ : closedBall z₀ r₁ ⊆ U := (closedBall_subset_closedBall hr₁₂.le).trans hcl₂
  obtain ⟨-, M, hM⟩ := KAM.han_margin hU hf hr₁0 hcl₁
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ (mem_closedBall_self hr₁0.le))
  obtain ⟨c, hc1, hc2⟩ := exists_powerSeries_coeff_banach hU hf hr₁0 hcl₁
  have hcb : ∀ α : Fin n → ℕ, ‖c α‖ ≤ M / r₁ ^ (∑ j, α j) := hc1 M hM
  have hdom : ∀ z ∈ ball z₀ r₁, ∀ α : Fin n → ℕ,
      ‖(∏ j, (z j - z₀ j) ^ α j) • c α‖ ≤ M * (‖z - z₀‖ / r₁) ^ (∑ j, α j) := by
    intro z hz α
    have hprod : ∏ j, ‖z j - z₀ j‖ ^ α j ≤ ‖z - z₀‖ ^ (∑ j, α j) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun j _ => by positivity)
        (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (z - z₀) j) _)
    calc ‖(∏ j, (z j - z₀ j) ^ α j) • c α‖
        = (∏ j, ‖z j - z₀ j‖ ^ α j) * ‖c α‖ := by simp only [norm_smul, norm_pow, norm_prod]
      _ ≤ ‖z - z₀‖ ^ (∑ j, α j) * (M / r₁ ^ (∑ j, α j)) :=
          mul_le_mul hprod (hcb α) (norm_nonneg _) (by positivity)
      _ = M * (‖z - z₀‖ / r₁) ^ (∑ j, α j) := by rw [div_pow]; ring
  have hsumm : ∀ z ∈ ball z₀ r₁,
      Summable (fun α : Fin n → ℕ => ‖(∏ j, (z j - z₀ j) ^ α j) • c α‖) := by
    intro z hz
    have ht1 : ‖z - z₀‖ / r₁ < 1 := by
      rw [div_lt_one hr₁0]
      simpa [mem_ball, dist_eq_norm] using hz
    exact Summable.of_nonneg_of_le (fun α => norm_nonneg _) (hdom z hz)
      ((KAM.hasSum_pow_sum n (by positivity) ht1).summable.mul_left M)
  have hpb : ∀ m : ℕ, ‖degreeSeries c m‖ ≤
      ((Finset.Nat.antidiagonalTuple n m).card : ℝ) * (M / r₁ ^ m) := fun m =>
    norm_degreeSeries_le c m fun α hα => by simpa [hα] using hcb α
  have hcard : ∀ m : ℕ, (Finset.Nat.antidiagonalTuple n m).card = (m + n - 1).choose (n - 1) := by
    intro m
    rw [card_antidiagonalTuple, show n + m - 1 = n - 1 + m by omega,
      show m + n - 1 = n - 1 + m by omega]
    exact Nat.choose_symm_add.symm
  refine ⟨r₁, hr₁, M, hM0, hcl₁, hM, c, hcb, fun z hz => ⟨hsumm z hz, hc2 z hz⟩,
    degreeSeries c, fun m => by rw [← hcard]; exact hpb m, fun m h => degreeSeries_apply_diag c m h,
    ?_, ?_, ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ => ?_
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr₁0] at hρ
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    have h0 : 0 ≤ (ρ : ℝ) / r₁ := by positivity
    have h1 : (ρ : ℝ) / r₁ < 1 := by rw [div_lt_one hr₁0]; exact hρ
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_card_mul_pow n h0 h1).mul_left M)
    calc ‖degreeSeries c m‖ * (ρ : ℝ) ^ m
        ≤ ((Finset.Nat.antidiagonalTuple n m).card : ℝ) * (M / r₁ ^ m) * (ρ : ℝ) ^ m := by
          gcongr; exact hpb m
      _ = M * (((Finset.Nat.antidiagonalTuple n m).card : ℝ) * ((ρ : ℝ) / r₁) ^ m) := by
          rw [div_pow]; field_simp
  · simpa using hr₁0
  · intro y hy
    have hy' : ‖y‖ < r₁ := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
        ENNReal.ofReal_lt_ofReal_iff hr₁0] at hy
      exact hy
    have hz : z₀ + y ∈ ball z₀ r₁ := by simpa [mem_ball, dist_eq_norm] using hy'
    have h := (hc2 (z₀ + y) hz).tsum_fiberwise (fun α : Fin n → ℕ => ∑ i, α i)
    have e : ∀ m, ∑' α : (fun α : Fin n → ℕ => ∑ i, α i) ⁻¹' {m},
        (∏ j, ((z₀ + y) j - z₀ j) ^ (α : Fin n → ℕ) j) • c α = degreeSeries c m (fun _ => y) :=
      fun m => by
      rw [tsum_degree_fiber (fun α : Fin n → ℕ => (∏ j, ((z₀ + y) j - z₀ j) ^ α j) • c α) m,
        degreeSeries_apply_diag]
      simp
    rw [funext fun m => (e m).symm]
    exact h


/-- Blueprint `bpW:w1:holo-analytic-fd`, real clause (step `stepW:w1:hareal`): if `f` is
holomorphic on `U ⊆ ℂⁿ` with values in a complex Banach space `F`, and real on the real points of
`U` with respect to a real-linear section pair `ι₂ : G → F`, `re₂ : F → G`, then
`re₂ ∘ f |_{U ∩ ℝⁿ}` is real analytic into `G`. -/
theorem holomorphic_real_part_analytic {n : ℕ} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {U : Set (Fin n → ℂ)} (hU : IsOpen U) {f : (Fin n → ℂ) → F}
    (hf : DifferentiableOn ℂ f U) (ι₂ : G →L[ℝ] F) (re₂ : F →L[ℝ] G) (hre : ∀ w, re₂ (ι₂ w) = w)
    (hreal : ∀ x : Fin n → ℝ, KAM.realInclusion n x ∈ U → ∃ w, f (KAM.realInclusion n x) = ι₂ w) :
    AnalyticOnNhd ℝ (fun x : Fin n → ℝ => re₂ (f (KAM.realInclusion n x)))
      (KAM.realInclusion n ⁻¹' U) := fun _ hx =>
  (analyticAt_real_part (KAM.realInclusion n) ι₂ re₂ hre
    (analyticOnNhd_of_differentiableOn_banach hU hf _ hx)
    (Filter.mem_of_superset ((hU.preimage (KAM.realInclusion n).continuous).mem_nhds hx)
      fun y hy => hreal y hy)).1

end KAM.Wave
