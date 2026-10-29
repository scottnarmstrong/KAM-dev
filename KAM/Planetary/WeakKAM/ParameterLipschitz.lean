/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Displacement
public import KAM.Planetary.WeakKAM.LimitSeries

/-! # P11B parameter Lipschitz: `collar_increment_lipschitz` and `lipschitz_family`

The one-stage short/long-distance dichotomy (`stepP:p11a:lf-stage`): for a holomorphic map bounded
by `e` on the collar `actionNbhd K t`, `‖g b - g b'‖ ≤ 4e/t ‖b - b'‖` for `b, b' ∈ K`. The short
case uses the Cauchy estimate on a max-norm polydisc of radius `t/2`; the long case the sup bound.
The telescoping and summation (`lf-tel`, `lf-sum`) use `param_lip_sum`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function Metric
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem collar_real_sub (b b' : SelectionR n) :
    selectionReal b - selectionReal b' = selectionReal (b - b') := by
  funext i; simp [selectionReal]

/-- Local analytic lemma used by lf-stage; no geometry of the closed set is needed. -/
theorem collar_increment_lipschitz (K : Set (SelectionR n)) (t e : ℝ)
    (ht : 0 < t) (he : 0 ≤ e) (g : SelectionC n → SelectionPhaseC n)
    (hg : DifferentiableOn ℂ g (actionNbhd K t))
    (hb : ∀ z ∈ actionNbhd K t, ‖g z‖ ≤ e) :
    ∀ b ∈ K, ∀ b' ∈ K,
      ‖g (selectionReal b) - g (selectionReal b')‖ ≤ 4 * e / t * ‖b - b'‖ := by
  intro b hb0 b' hb'
  have hmem : ∀ x ∈ K, selectionReal x ∈ actionNbhd K t := fun x hx =>
    ⟨x, hx, by simpa using ht⟩
  have hnn : 0 ≤ ‖b - b'‖ := norm_nonneg _
  by_cases hfar : t / 2 ≤ ‖b - b'‖
  · have h2 : ‖g (selectionReal b) - g (selectionReal b')‖ ≤ 2 * e :=
      (norm_sub_le _ _).trans (by linarith [hb _ (hmem b hb0), hb _ (hmem b' hb')])
    refine h2.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ ht]
    nlinarith
  · push_neg at hfar
    have hU : IsOpen (actionNbhd K t) := p11_isOpen_actionNbhd K t
    have hseg : ∀ x ∈ segment ℝ (selectionReal b) (selectionReal b'),
        closedBall x (t / 2) ⊆ actionNbhd K t := by
      intro x hx w hw
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hx
      refine ⟨b, hb0, ?_⟩
      have e1 : α • selectionReal b + β • selectionReal b' - selectionReal b =
          β • (selectionReal b' - selectionReal b) := by
        rw [show α = 1 - β by linarith, sub_smul, one_smul, smul_sub]; abel
      have h1 : ‖α • selectionReal b + β • selectionReal b' - selectionReal b‖ ≤ ‖b - b'‖ := by
        rw [e1, norm_smul, ← norm_neg (selectionReal b' - selectionReal b), neg_sub,
          collar_real_sub, norm_selectionReal, Real.norm_of_nonneg hβ]
        nlinarith
      rw [mem_closedBall, dist_eq_norm] at hw
      calc ‖w - selectionReal b‖ = ‖(w - (α • selectionReal b + β • selectionReal b')) +
            (α • selectionReal b + β • selectionReal b' - selectionReal b)‖ := by congr 1; abel
        _ < t := by linarith [norm_add_le (w - (α • selectionReal b + β • selectionReal b'))
            (α • selectionReal b + β • selectionReal b' - selectionReal b)]
    have hder : ∀ x ∈ segment ℝ (selectionReal b) (selectionReal b'),
        ‖fderiv ℂ g x‖ ≤ e / (t / 2) := fun x hx =>
      KAM.norm_fderiv_le_of_closedBall hU hg (half_pos ht) (hseg x hx) hb
    have hfd : ∀ x ∈ segment ℝ (selectionReal b) (selectionReal b'),
        HasFDerivWithinAt g ((fderiv ℂ g x).restrictScalars ℝ)
          (segment ℝ (selectionReal b) (selectionReal b')) x := fun x hx =>
      ((hg.differentiableAt (hU.mem_nhds
        (hseg x hx (mem_closedBall_self (half_pos ht).le)))).hasFDerivAt.restrictScalars
          ℝ).hasFDerivWithinAt
    have hmv := (convex_segment (selectionReal b) (selectionReal b')).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := g) (f' := fun x => (fderiv ℂ g x).restrictScalars ℝ) hfd
      (fun x hx => by
        rw [ContinuousLinearMap.norm_restrictScalars]; exact hder x hx)
      (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
    rw [collar_real_sub, norm_selectionReal] at hmv
    refine hmv.trans ?_
    have : e / (t / 2) ≤ 4 * e / t := by
      rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right ht]; linarith
    exact mul_le_mul_of_nonneg_right this hnn

structure SelectionLipschitz (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (ε : ℝ) extends SelectionDisplacement d f ε where
  lipschitz_separate : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    ‖defect b θ - defect b' θ'‖ ≤
      (2 : ℝ)⁻¹ ^ 11 * ‖θ - θ'‖ + (2 : ℝ)⁻¹ ^ 11 * ‖b - b'‖
  lipschitz_joint : ∀ b ∈ Kinf, ∀ b' ∈ Kinf, ∀ θ θ',
    ‖defect b θ - defect b' θ'‖ ≤ (2 : ℝ)⁻¹ ^ 10 * ‖((θ, b) : Phase n) - (θ', b')‖

section Stage
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (cx : WeakBudgetCtx d a) (c : SelectionComposition d f a) {b b' : SelectionR n}

include cx

theorem lipFam_t_succ_le (j : ℕ) : selectiont a (j + 1) ≤ selectiont a j := by
  have h := cx.hyp
  have hx : ((2 : ℝ) ^ (a.τ + 1))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) (by linarith [h.hτ]))
  rw [selectiont_eq, selectiont_eq, pow_succ]
  have h0 : 0 ≤ (((2 : ℝ) ^ (a.τ + 1))⁻¹) ^ j := by positivity
  nlinarith [h.ht]

/-- Step `lf-stage` of `bpP:p11a:lipschitz-family`, for the parameter increment of one stage. -/
theorem lipFam_stage (hb : b ∈ c.Kinf) (hb' : b' ∈ c.Kinf) (θ : SelectionR n) (j : ℕ) :
    ‖selectionLimInc c.toSelectionChain b j (selectionReal θ) -
      selectionLimInc c.toSelectionChain b' j (selectionReal θ)‖ ≤
      4 * selectionLimBound a j / selectiont a (j + 1) * ‖b - b'‖ := by
  set z0 : SelectionPhaseC n := (selectionReal θ, 0) with hz0
  set g : SelectionC n → SelectionPhaseC n := fun β =>
    selectionCompose c.toSelectionChain β (j + 1) z0 - selectionCompose c.toSelectionChain β j z0
    with hg
  have hKinf : ∀ ν, c.Kinf ⊆ c.K ν := fun ν x hx => by
    have : x ∈ ⋂ j, c.K j := c.Kinf_eq ▸ hx
    exact mem_iInter.1 this ν
  have hθ : selectionReal θ ∈ complexStrip n (a.strip / 2) :=
    selectionReal_mem_complexStrip (by linarith [cx.hyp.hstrip]) θ
  have ht1 := wbud_t_pos cx (j + 1)
  have hdom : ∀ ν, selectiont a (j + 1) ≤ selectiont a ν → ∀ β ∈ actionNbhd c.Kinf (selectiont a (j + 1)),
      (z0, β) ∈ selectionDomain (selectionr a ν) (selections a ν)
        (actionNbhd (c.K ν) (selectiont a ν)) := fun ν hν β hβ => by
    obtain ⟨J, hJ, hd⟩ := hβ
    refine ⟨fun i => (hθ i).trans_le (iter_strip cx ν).1, ?_, J, hKinf ν hJ, hd.trans_le hν⟩
    simpa using wbud_s_pos cx.hyp ν
  have hd1 : ∀ β ∈ actionNbhd c.Kinf (selectiont a (j + 1)),
      (z0, β) ∈ selectionDomain (selectionr a (j + 1)) (selections a (j + 1))
        (actionNbhd (c.K (j + 1)) (selectiont a (j + 1))) := fun β hβ => hdom (j + 1) le_rfl β hβ
  have hd0 : ∀ β ∈ actionNbhd c.Kinf (selectiont a (j + 1)),
      (z0, β) ∈ selectionDomain (selectionr a j) (selections a j)
        (actionNbhd (c.K j) (selectiont a j)) := fun β hβ =>
    hdom j (lipFam_t_succ_le cx j) β hβ
  have hpt : Differentiable ℂ (fun β : SelectionC n => (z0, β)) :=
    (differentiable_const z0).prodMk differentiable_id
  have hdiff : DifferentiableOn ℂ g (actionNbhd c.Kinf (selectiont a (j + 1))) :=
    ((c.composition_holo (j + 1)).comp hpt.differentiableOn hd1).sub
      ((c.composition_holo j).comp hpt.differentiableOn hd0)
  have hbd : ∀ β ∈ actionNbhd c.Kinf (selectiont a (j + 1)), ‖g β‖ ≤ selectionLimBound a j :=
    fun β hβ => c.composition_increment j (z0, β) (hd1 β hβ)
  exact collar_increment_lipschitz c.Kinf (selectiont a (j + 1)) (selectionLimBound a j) ht1
    (selectionLim_bound_nonneg cx j) g hdiff hbd b hb b' hb'

end Stage

section Family
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

theorem lipFam_alpha_nonneg (cx : WeakBudgetCtx d a) (j : ℕ) : 0 ≤ selectionAlpha a j := by
  have := wbud_s_pos cx.hyp j
  have hk := (wbud_stage cx.hyp j).2.2.2.1
  rw [(wbud_stage cx.hyp j).2.2.2.2.2.1]
  positivity

/-- Steps `lf-tel`, `lf-sum`: the limit map is `2⁻¹¹`-Lipschitz in the parameter. -/
theorem lipFam_limit (cx : WeakBudgetCtx d a)
    (hsum : (∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ≤
      (2 : ℝ)⁻¹ ^ 10 / 16)
    (hsumm : Summable (fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)))
    (L : SelectionLimit d f a) {b b' : SelectionR n} (hb : b ∈ L.Kinf) (hb' : b' ∈ L.Kinf)
    (θ : SelectionR n) :
    ‖L.limitC b (selectionReal θ) - L.limitC b' (selectionReal θ)‖ ≤
      (2 : ℝ)⁻¹ ^ 11 * ‖b - b'‖ := by
  have hs := cx.hyp.hstrip
  have hst : d.strip = a.strip := cx.hstrip.symm
  have hθ : selectionReal θ ∈ complexStrip n (d.strip / 4) :=
    selectionReal_mem_complexStrip (by rw [hst]; linarith) θ
  set v : ℕ → ℝ := fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) with hv
  have hv0 : ∀ j, 0 ≤ v j := fun j => by
    have := (wbud_stage cx.hyp j).2.1
    have := lipFam_alpha_nonneg cx j
    have := wbud_t_pos cx (j + 1)
    positivity
  have hw : ∀ j, 4 * selectionLimBound a j / selectiont a (j + 1) ≤
      4 * (1 + (2 : ℝ)⁻¹ ^ 11) * v j := fun j => by
    have ht := wbud_t_pos cx (j + 1)
    have hm : max (selectionA a j) (selectionAlpha a j) ≤ selectionA a j + selectionAlpha a j :=
      max_le (by linarith [lipFam_alpha_nonneg cx j]) (by linarith [(wbud_stage cx.hyp j).2.1])
    have : selectionLimBound a j ≤ (1 + (2 : ℝ)⁻¹ ^ 11) * (selectionA a j + selectionAlpha a j) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    rw [hv]
    simp only
    rw [div_le_iff₀ ht, mul_assoc, mul_div_assoc', div_mul_cancel₀ _ ht.ne']
    linarith
  have hstage : ∀ ν, ‖selectionLimStage L.toSelectionChain b ν (selectionReal θ) -
      selectionLimStage L.toSelectionChain b' ν (selectionReal θ)‖ ≤
      (4 * (1 + (2 : ℝ)⁻¹ ^ 11) * ∑' j, v j) * ‖b - b'‖ := fun ν => by
    rw [selectionLimStage_eq_sum, selectionLimStage_eq_sum, add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Finset.range ν, ‖selectionLimInc L.toSelectionChain b j (selectionReal θ) -
          selectionLimInc L.toSelectionChain b' j (selectionReal θ)‖
        ≤ ∑ j ∈ Finset.range ν, (4 * (1 + (2 : ℝ)⁻¹ ^ 11) * v j) * ‖b - b'‖ :=
          Finset.sum_le_sum fun j _ => (lipFam_stage cx L.toSelectionComposition hb hb' θ j).trans
            (mul_le_mul_of_nonneg_right (hw j) (norm_nonneg _))
      _ = (4 * (1 + (2 : ℝ)⁻¹ ^ 11) * ∑ j ∈ Finset.range ν, v j) * ‖b - b'‖ := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (hsumm.sum_le_tsum _ fun j _ => hv0 j) (by positivity)) (norm_nonneg _)
  have h1 := (L.limit_uniform b hb).tendsto_at hθ
  have h2 := (L.limit_uniform b' hb').tendsto_at hθ
  have hlim := le_of_tendsto' ((h1.sub h2).norm) hstage
  refine hlim.trans ?_
  have hc : 4 * (1 + (2 : ℝ)⁻¹ ^ 11) * ∑' j, v j ≤ (2 : ℝ)⁻¹ ^ 11 := by
    have h0 : 0 ≤ ∑' j, v j := tsum_nonneg hv0
    have : 4 * (1 + (2 : ℝ)⁻¹ ^ 11) * ∑' j, v j ≤
        4 * (1 + (2 : ℝ)⁻¹ ^ 11) * ((2 : ℝ)⁻¹ ^ 10 / 16) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    exact this.trans (by norm_num)
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

end Family

theorem lipschitz_family (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionLipschitz d f ε) := by
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  have cx := weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he'
  obtain ⟨hsumm, hsum⟩ := param_lip_sum d ε he hsmall
  obtain ⟨L⟩ := displacement d ε he hsmall f hf
  have key : ∀ b ∈ L.Kinf, ∀ b' ∈ L.Kinf, ∀ θ,
      ‖L.defect b θ - L.defect b' θ‖ ≤ (2 : ℝ)⁻¹ ^ 11 * ‖b - b'‖ := fun b hb b' hb' θ => by
    have h := lipFam_limit cx hsum hsumm L.toSelectionLimit hb hb' θ
    have e : L.limitC b (selectionReal θ) - L.limitC b' (selectionReal θ) =
        phaseToC (L.defect b θ - L.defect b' θ) := by
      rw [L.limit_real b hb θ, L.limit_real b' hb' θ]
      simp only [phaseToC_eq_realInclusion₂]
      rw [← map_sub]
      congr 1
      abel
    rwa [e, phaseToC_eq_realInclusion₂, norm_realInclusion₂] at h
  have sep : ∀ b ∈ L.Kinf, ∀ b' ∈ L.Kinf, ∀ θ θ',
      ‖L.defect b θ - L.defect b' θ'‖ ≤
        (2 : ℝ)⁻¹ ^ 11 * ‖θ - θ'‖ + (2 : ℝ)⁻¹ ^ 11 * ‖b - b'‖ := fun b hb b' hb' θ θ' =>
    (norm_sub_le_norm_sub_add_norm_sub (L.defect b θ) (L.defect b θ') (L.defect b' θ')).trans
      (add_le_add (L.angle_lipschitz b hb θ θ') (key b hb b' hb' θ'))
  refine ⟨{ L with
    lipschitz_separate := sep
    lipschitz_joint := fun b hb b' hb' θ θ' => ?_ }⟩
  have h1 := sep b hb b' hb' θ θ'
  have hM : ‖((θ, b) : Phase n) - (θ', b')‖ = max ‖θ - θ'‖ ‖b - b'‖ := by
    rw [Prod.norm_def]; rfl
  rw [hM]
  have hk : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 11 := by positivity
  have e2 : (2 : ℝ)⁻¹ ^ 10 = 2 * (2 : ℝ)⁻¹ ^ 11 := by norm_num
  have a1 := mul_le_mul_of_nonneg_left (le_max_left ‖θ - θ'‖ ‖b - b'‖) hk
  have a2 := mul_le_mul_of_nonneg_left (le_max_right ‖θ - θ'‖ ‖b - b'‖) hk
  rw [e2]
  linarith

end KAM.Planetary

end
