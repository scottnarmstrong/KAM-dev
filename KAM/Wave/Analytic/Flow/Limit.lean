/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.PicardHolo
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The flow as a limit of Picard iterates

Blueprint-W `bpW:w1:flow`, step `stepW:w1:flowlim` (package W1-ANALYTIC). This is source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

`KAM.Wave.holoFlow X t w = w + ∑' k, (φ_{k+1}(w, t) - φ_k(w, t))` is the limit of the Picard
iterates,
uniformly in `w ∈ U` (for fixed `t ∈ [-1, 1]`) and uniformly in `t ∈ [-1, 1]` (for fixed `w ∈ U`).
It satisfies `‖holoFlow X t w - w‖ ≤ M |t|` and the integral equation
`holoFlow X t w = w + ∫₀ᵗ X (holoFlow X σ w) dσ`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The limit of the Picard iterates (blueprint `bpW:w1:flow`). -/
def holoFlow (X : F → F) (t : ℝ) (w : F) : F :=
  w + ∑' k : ℕ, (wavePicard X w (k + 1) t - wavePicard X w k t)

theorem tendstoUniformlyOn_of_succ_sub {β : Type*} {f : ℕ → β → F} {s : Set β} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ k x, x ∈ s → ‖f (k + 1) x - f k x‖ ≤ u k) :
    TendstoUniformlyOn f (fun x => f 0 x + ∑' k, (f (k + 1) x - f k x)) atTop s := by
  have h := tendstoUniformlyOn_tsum_nat (f := fun k x => f (k + 1) x - f k x) hu hf
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with K hK x hx
  have := hK x hx
  have e : f K x = f 0 x + ∑ k ∈ Finset.range K, (f (k + 1) x - f k x) := by
    have := Finset.sum_range_sub (fun i => f i x) K
    rw [this]; abel
  rw [e, dist_add_left]
  exact this

variable {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

omit [CompleteSpace F] in
theorem summable_picard_bound :
    Summable fun k : ℕ => M * ((M / δ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg h.M_pos.le
    (div_nonneg (pow_nonneg hL k) (by positivity))) (fun k => ?_)
    ((Real.summable_pow_div_factorial (M / δ)).mul_left M)
  refine mul_le_mul_of_nonneg_left ?_ h.M_pos.le
  refine div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.factorial_pos _) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ k)

omit [CompleteSpace F] in
theorem norm_picard_succ_sub_le_bound {w : F} (hw : w ∈ U) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖wavePicard X w (k + 1) t - wavePicard X w k t‖ ≤
      M * ((M / δ) ^ k / ((k + 1).factorial : ℝ)) := by
  refine (norm_picard_succ_sub_le h hw k t ht).trans ?_
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have : |t| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) (abs_le.mpr ⟨ht.1, ht.2⟩)
  calc M * (M / δ) ^ k * |t| ^ (k + 1) / ((k + 1).factorial : ℝ)
      ≤ M * (M / δ) ^ k * 1 / ((k + 1).factorial : ℝ) := by
        gcongr
        exact mul_nonneg h.M_pos.le (pow_nonneg hL k)
    _ = M * ((M / δ) ^ k / ((k + 1).factorial : ℝ)) := by ring

/-- Uniform convergence of the iterates in `w`, for fixed `t`. -/
theorem tendstoUniformlyOn_picard_U {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    TendstoUniformlyOn (fun K w => wavePicard X w K t) (holoFlow X t) atTop U :=
  tendstoUniformlyOn_of_succ_sub (f := fun K w => wavePicard X w K t) (summable_picard_bound h)
    fun k w hw => norm_picard_succ_sub_le_bound h hw k ht

/-- Uniform convergence of the iterates in `t`, for fixed `w`. -/
theorem tendstoUniformlyOn_picard_time {w : F} (hw : w ∈ U) :
    TendstoUniformlyOn (fun K t => wavePicard X w K t) (fun t => holoFlow X t w) atTop
      (Icc (-1) 1) :=
  tendstoUniformlyOn_of_succ_sub (f := fun K t => wavePicard X w K t) (summable_picard_bound h)
    fun k t ht => norm_picard_succ_sub_le_bound h hw k ht

theorem tendsto_picard {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun K => wavePicard X w K t) atTop (𝓝 (holoFlow X t w)) :=
  (tendstoUniformlyOn_picard_U h ht).tendsto_at hw

theorem norm_holoFlow_sub_le {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖holoFlow X t w - w‖ ≤ M * |t| :=
  le_of_tendsto ((tendsto_picard h hw ht).sub_const w).norm
    (Eventually.of_forall fun K => (norm_picard_sub_le h hw K).1 t ht)

theorem holoFlow_mem_ball {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    holoFlow X t w ∈ ball w δ := by
  rw [mem_ball_iff_norm]
  refine lt_of_le_of_lt (norm_holoFlow_sub_le h hw ht) ?_
  have : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  nlinarith [h.M_lt, h.M_pos]

theorem holoFlow_zero {w : F} (hw : w ∈ U) : holoFlow X 0 w = w := by
  have := norm_holoFlow_sub_le h hw (t := 0) ⟨by norm_num, by norm_num⟩
  rw [abs_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] at this
  exact this

theorem continuousOn_holoFlow_time {w : F} (hw : w ∈ U) :
    ContinuousOn (fun t => holoFlow X t w) (Icc (-1) 1) :=
  (tendstoUniformlyOn_picard_time h hw).continuousOn
    (Eventually.frequently (Eventually.of_forall fun K => (norm_picard_sub_le h hw K).2))

theorem continuousOn_X_holoFlow {w : F} (hw : w ∈ U) :
    ContinuousOn (fun t => X (holoFlow X t w)) (Icc (-1) 1) :=
  h.continuousOn_X.comp (continuousOn_holoFlow_time h hw) fun _ ht =>
    h.mem_V_of_ball hw (holoFlow_mem_ball h hw ht)

/-- The integral equation `Φ^t(w) = w + ∫₀ᵗ X (Φ^σ(w)) dσ`. -/
theorem holoFlow_eq_integral {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    holoFlow X t w = w + ∫ σ in (0 : ℝ)..t, X (holoFlow X σ w) := by
  have h1 : Tendsto (fun K => wavePicard X w (K + 1) t) atTop (𝓝 (holoFlow X t w)) :=
    (tendsto_picard h hw ht).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun K => w + ∫ σ in (0 : ℝ)..t, X (wavePicard X w K σ)) atTop
      (𝓝 (w + ∫ σ in (0 : ℝ)..t, X (holoFlow X σ w))) := by
    refine tendsto_const_nhds.add ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun K => ?_) (Eventually.of_forall fun K => ?_) intervalIntegrable_const
      (Eventually.of_forall fun σ hσ => ?_)
    · exact ((continuousOn_X_picard h hw K).mono (uIoc_subset_Icc ht)).aestronglyMeasurable
        measurableSet_uIoc
    · exact Eventually.of_forall fun σ hσ => h.bound _ (h.mem_V_of_ball hw (picard_mem_ball h hw K
        (uIoc_subset_Icc ht hσ)))
    · have hσ' := uIoc_subset_Icc ht hσ
      exact ((h.continuousOn_X.continuousAt (h.isOpen_V.mem_nhds
        (h.mem_V_of_ball hw (holoFlow_mem_ball h hw hσ')))).tendsto).comp (tendsto_picard h hw hσ')
  exact tendsto_nhds_unique h1 h2

end KAM.Wave
