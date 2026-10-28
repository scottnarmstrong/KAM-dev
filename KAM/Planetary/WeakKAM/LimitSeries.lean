/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Composition
public import KAM.Strip.Cauchy
public import KAM.Strip.Limits

/-! # P11B limit map: fixed-strip series of the compositions

For `b ∈ K_∞` the zero-section compositions `θ ↦ C_ν(θ, 0)` differ by at most
`(1 + 2⁻¹¹) max (A_ν, α_ν)` on the strip `T_(s/2)` (source step `lm-inc`); the Cauchy estimate
on the strictly smaller strip `T_(s/4)` bounds the derivative increments by the same quantity
divided by `s/4` (`lm-der`). Both series are summable, so values and derivatives converge
uniformly on `T_(s/4)`, and `KAM.uniform_limits` identifies the derivative of the limit (`lm-hol`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The zero-section composition `θ ↦ C_ν(θ, 0)` at the real parameter `b`. -/
def selectionLimStage (c : SelectionChain n) (b : SelectionR n) (ν : ℕ) (θ : SelectionC n) :
    SelectionPhaseC n :=
  selectionCompose c (selectionReal b) ν (θ, 0)

/-- The increment `C_{j+1}(θ, 0) - C_j(θ, 0)`. -/
def selectionLimInc (c : SelectionChain n) (b : SelectionR n) (j : ℕ) (θ : SelectionC n) :
    SelectionPhaseC n :=
  selectionLimStage c b (j + 1) θ - selectionLimStage c b j θ

/-- The derivative increment of consecutive zero-section compositions. -/
def selectionLimDInc (c : SelectionChain n) (b : SelectionR n) (j : ℕ) (θ : SelectionC n) :
    SelectionC n →L[ℂ] SelectionPhaseC n :=
  fderiv ℂ (selectionLimStage c b (j + 1)) θ - fderiv ℂ (selectionLimStage c b j) θ

/-- The zero-section limit map. -/
def selectionLimMap (c : SelectionChain n) (b : SelectionR n) (θ : SelectionC n) :
    SelectionPhaseC n :=
  (θ, 0) + ∑' j, selectionLimInc c b j θ

/-- The limit of the derivatives. -/
def selectionLimDMap (c : SelectionChain n) (b : SelectionR n) (θ : SelectionC n) :
    SelectionC n →L[ℂ] SelectionPhaseC n :=
  ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) + ∑' j, selectionLimDInc c b j θ

/-- The stage bound of the increments. -/
def selectionLimBound (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  (1 + (2 : ℝ)⁻¹ ^ 11) * max (selectionA a j) (selectionAlpha a j)

theorem selectionLimStage_zero (c : SelectionChain n) (b : SelectionR n) (θ : SelectionC n) :
    selectionLimStage c b 0 θ = (θ, 0) := rfl

theorem selectionLimStage_eq_sum (c : SelectionChain n) (b : SelectionR n) (ν : ℕ)
    (θ : SelectionC n) :
    selectionLimStage c b ν θ = (θ, 0) + ∑ j ∈ Finset.range ν, selectionLimInc c b j θ := by
  have h : ∑ j ∈ Finset.range ν, selectionLimInc c b j θ =
      selectionLimStage c b ν θ - selectionLimStage c b 0 θ :=
    Finset.sum_range_sub (fun j => selectionLimStage c b j θ) ν
  rw [h, selectionLimStage_zero]
  abel

section Estimates
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (cx : WeakBudgetCtx d a) (c : SelectionComposition d f a) {b : SelectionR n}

include cx

theorem selectionLim_mem (hb : b ∈ c.Kinf) (ν : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 2)) :
    ((θ, 0), selectionReal b) ∈ selectionDomain (selectionr a ν) (selections a ν)
      (actionNbhd (c.K ν) (selectiont a ν)) := by
  have hr := (iter_strip cx ν).1
  refine ⟨fun i => (hθ i).trans_le hr, ?_, ?_⟩
  · simpa using wbud_s_pos cx.hyp ν
  · have hbK : b ∈ c.K ν := by
      have : b ∈ ⋂ j, c.K j := c.Kinf_eq ▸ hb
      exact mem_iInter.1 this ν
    refine ⟨b, hbK, ?_⟩
    rw [show selectionReal b - (fun i => ((b i : ℝ) : ℂ)) = 0 from sub_self _, norm_zero]
    exact wbud_t_pos cx ν

theorem selectionLim_diffOn (hb : b ∈ c.Kinf) (ν : ℕ) :
    DifferentiableOn ℂ (selectionLimStage c.toSelectionChain b ν)
      (complexStrip n (a.strip / 2)) := by
  have hmap : MapsTo (fun θ : SelectionC n => ((θ, (0 : SelectionC n)), selectionReal b))
      (complexStrip n (a.strip / 2)) (selectionDomain (selectionr a ν) (selections a ν)
        (actionNbhd (c.K ν) (selectiont a ν))) := fun θ hθ => selectionLim_mem cx c hb ν hθ
  have hg : Differentiable ℂ
      (fun θ : SelectionC n => ((θ, (0 : SelectionC n)), selectionReal b)) :=
    (differentiable_id.prodMk (differentiable_const (0 : SelectionC n))).prodMk
      (differentiable_const _)
  exact (c.composition_holo ν).comp hg.differentiableOn hmap

theorem selectionLim_diffAt (hb : b ∈ c.Kinf) (ν : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 2)) :
    DifferentiableAt ℂ (selectionLimStage c.toSelectionChain b ν) θ :=
  (selectionLim_diffOn cx c hb ν).differentiableAt
    ((KAM.isOpen_complexStrip n _).mem_nhds hθ)

theorem selectionLim_inc_bound (hb : b ∈ c.Kinf) (j : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 2)) :
    ‖selectionLimInc c.toSelectionChain b j θ‖ ≤ selectionLimBound a j :=
  by
  have h := c.composition_increment j ((θ, 0), selectionReal b)
    (selectionLim_mem cx c hb (j + 1) hθ)
  exact h

theorem selectionLim_bound_nonneg (j : ℕ) : 0 ≤ selectionLimBound a j := by
  have := (wbud_stage cx.hyp j).2.1
  unfold selectionLimBound
  have h : 0 ≤ max (selectionA a j) (selectionAlpha a j) := le_max_of_le_left this
  positivity

theorem selectionLim_bound_summable : Summable (selectionLimBound a) := by
  obtain ⟨hA, hα, -, -⟩ := wbud_sums_Aα cx
  refine Summable.of_nonneg_of_le (selectionLim_bound_nonneg cx) (fun j => ?_)
    ((hA.add hα).mul_left (1 + (2 : ℝ)⁻¹ ^ 11))
  have hA0 := (wbud_stage cx.hyp j).2.1
  have hα0 : 0 ≤ selectionAlpha a j := by
    have := wbud_s_pos cx.hyp j
    have hk := (wbud_stage cx.hyp j).2.2.2.1
    rw [(wbud_stage cx.hyp j).2.2.2.2.2.1]
    positivity
  unfold selectionLimBound
  have : max (selectionA a j) (selectionAlpha a j) ≤ selectionA a j + selectionAlpha a j :=
    max_le (by linarith) (by linarith)
  gcongr

theorem selectionLim_dinc_bound (hb : b ∈ c.Kinf) (j : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    ‖selectionLimDInc c.toSelectionChain b j θ‖ ≤ selectionLimBound a j / (a.strip / 4) := by
  have hs := cx.hyp.hstrip
  have hθ2 : θ ∈ complexStrip n (a.strip / 2) := fun i => (hθ i).trans (by linarith)
  have hd : ∀ ν, DifferentiableAt ℂ (selectionLimStage c.toSelectionChain b ν) θ :=
    fun ν => selectionLim_diffAt cx c hb ν hθ2
  have hdiff : DifferentiableOn ℂ (selectionLimInc c.toSelectionChain b j)
      (complexStrip n (a.strip / 2)) :=
    (selectionLim_diffOn cx c hb (j + 1)).sub (selectionLim_diffOn cx c hb j)
  have hθ' : θ ∈ complexStrip n (a.strip / 2 - a.strip / 4) := by
    have : a.strip / 2 - a.strip / 4 = a.strip / 4 := by ring
    rwa [this]
  have h := KAM.norm_fderiv_le_of_mem_complexStrip hdiff
    (fun w hw => selectionLim_inc_bound cx c hb j hw) (by positivity : 0 < a.strip / 4) hθ'
  have e : fderiv ℂ (selectionLimInc c.toSelectionChain b j) θ =
      selectionLimDInc c.toSelectionChain b j θ :=
    fderiv_sub (hd (j + 1)) (hd j)
  rwa [e] at h

/-- Uniform convergence of the zero-section compositions on the strip `T_(s/4)`. -/
theorem selectionLim_unif (hb : b ∈ c.Kinf) :
    TendstoUniformlyOn (selectionLimStage c.toSelectionChain b)
      (selectionLimMap c.toSelectionChain b) atTop (complexStrip n (a.strip / 4)) := by
  have hs := cx.hyp.hstrip
  have h := tendstoUniformlyOn_tsum_nat (s := complexStrip n (a.strip / 4))
    (selectionLim_bound_summable cx)
    (f := selectionLimInc c.toSelectionChain b) (fun j θ hθ =>
      selectionLim_inc_bound cx c hb j (fun i => (hθ i).trans (by linarith)))
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN θ hθ
  have := hN θ hθ
  rw [selectionLimStage_eq_sum, selectionLimMap, dist_add_left]
  exact this

theorem selectionLim_stage_deriv_eq (_hb : b ∈ c.Kinf) (ν : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    fderiv ℂ (selectionLimStage c.toSelectionChain b ν) θ =
      ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) +
        ∑ j ∈ Finset.range ν, selectionLimDInc c.toSelectionChain b j θ := by
  have hs := cx.hyp.hstrip
  have hθ2 : θ ∈ complexStrip n (a.strip / 2) := fun i => (hθ i).trans (by linarith)
  have h : ∑ j ∈ Finset.range ν, selectionLimDInc c.toSelectionChain b j θ =
      fderiv ℂ (selectionLimStage c.toSelectionChain b ν) θ -
        fderiv ℂ (selectionLimStage c.toSelectionChain b 0) θ :=
    Finset.sum_range_sub (fun j => fderiv ℂ (selectionLimStage c.toSelectionChain b j) θ) ν
  rw [h]
  have h0 : fderiv ℂ (selectionLimStage c.toSelectionChain b 0) θ =
      ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) :=
    ((hasFDerivAt_id θ).prodMk (hasFDerivAt_const (0 : SelectionC n) θ)).fderiv
  rw [h0]
  abel

/-- Uniform convergence of the derivatives on the strip `T_(s/4)` (source step `lm-der`). -/
theorem selectionLim_dunif (hb : b ∈ c.Kinf) :
    TendstoUniformlyOn (fun ν θ => fderiv ℂ (selectionLimStage c.toSelectionChain b ν) θ)
      (selectionLimDMap c.toSelectionChain b) atTop (complexStrip n (a.strip / 4)) := by
  have hs := cx.hyp.hstrip
  have h := tendstoUniformlyOn_tsum_nat (s := complexStrip n (a.strip / 4))
    ((selectionLim_bound_summable cx).div_const (a.strip / 4))
    (f := selectionLimDInc c.toSelectionChain b)
    (fun j θ hθ => selectionLim_dinc_bound cx c hb j hθ)
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN θ hθ
  have := hN θ hθ
  rw [selectionLim_stage_deriv_eq cx c hb N hθ, selectionLimDMap, dist_add_left]
  exact this

/-- `lm-hol`: the limit is holomorphic on the fixed strip, with the limiting derivative. -/
theorem selectionLim_holo (hb : b ∈ c.Kinf) :
    DifferentiableOn ℂ (selectionLimMap c.toSelectionChain b) (complexStrip n (a.strip / 4)) ∧
      ∀ θ ∈ complexStrip n (a.strip / 4),
        fderiv ℂ (selectionLimMap c.toSelectionChain b) θ =
          selectionLimDMap c.toSelectionChain b θ := by
  have hs := cx.hyp.hstrip
  refine KAM.uniform_limits (KAM.isOpen_complexStrip n _)
    (K := selectionLimStage c.toSelectionChain b)
    (fun ν => (selectionLim_diffOn cx c hb ν).mono
      (fun θ hθ i => (hθ i).trans (by linarith)))
    (fun θ hθ => (selectionLim_unif cx c hb).tendsto_at hθ) (selectionLim_dunif cx c hb)

end Estimates

end KAM.Planetary

end
