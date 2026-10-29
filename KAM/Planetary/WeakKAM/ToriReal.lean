/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.ToriStage
public import KAM.Strip.RealRestriction

/-! # P11B tori: real restriction of the limit map

The limit map `limitC b` is holomorphic on `T_(s/4)` and real on real angles, so its real
restriction is the evaluation `θ ↦ (θ, b) + defect b θ` shifted by the constant `(0, b)`
(`selectionEvaluation`). From the strip theory: real analyticity and the relation
`ι (Dk h) = DK (ι h)`. Source steps `lt-lag` (Lagrangian, as the limit of the zero-section
pullback) and `lt-emb` (immersion and embedding from the angle-defect Lipschitz bound).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Real
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (L : SelectionLimit d f a) {b : SelectionR n}

theorem tori_isReal (hb : b ∈ L.Kinf) : IsRealOnReals (L.limitC b) := fun θ =>
  ⟨(θ, 0) + L.defect b θ, L.limit_real b hb θ⟩

theorem tori_rr_eq (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    realRestriction (L.limitC b) θ = (θ, 0) + L.defect b θ := by
  refine realInclusion₂_injective n ?_
  rw [← isRealOnReals_iff.mp (tori_isReal L hb) θ, ← tori_phaseToC_eq]
  exact L.limit_real b hb θ

theorem tori_eval_eq (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    selectionEvaluation L.defect b θ = realRestriction (L.limitC b) θ + (0, b) := by
  rw [tori_rr_eq L hb]
  unfold selectionEvaluation
  ext i <;> simp [add_assoc, add_comm]

theorem tori_strip_pos (hs : 0 < d.strip) : 0 < d.strip / 4 := by linarith

theorem tori_analytic (hb : b ∈ L.Kinf) :
    AnalyticOnNhd ℝ (selectionEvaluation L.defect b) univ := by
  have h := analyticOnNhd_realRestriction (tori_strip_pos d.strip_pos) (L.limit_holo b hb)
  have h2 : selectionEvaluation L.defect b = fun θ => realRestriction (L.limitC b) θ + (0, b) :=
    funext (tori_eval_eq L hb)
  rw [h2]
  exact h.add analyticOnNhd_const

theorem tori_fderiv_eval (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    fderiv ℝ (selectionEvaluation L.defect b) θ =
      fderiv ℝ (realRestriction (L.limitC b)) θ := by
  have h2 : selectionEvaluation L.defect b = fun θ => realRestriction (L.limitC b) θ + (0, b) :=
    funext (tori_eval_eq L hb)
  rw [h2]; exact fderiv_add_const _

theorem tori_fderiv_real (hb : b ∈ L.Kinf) (θ v : SelectionR n) :
    realInclusion₂ n (fderiv ℝ (selectionEvaluation L.defect b) θ v) =
      fderiv ℂ (L.limitC b) (selectionReal θ) (selectionReal v) := by
  rw [tori_fderiv_eval L hb]
  exact (realRestriction_fderiv (tori_strip_pos d.strip_pos) (L.limit_holo b hb)
    (tori_isReal L hb) θ).2 v

theorem tori_diffAt_eval (hb : b ∈ L.Kinf) (θ : SelectionR n) :
    DifferentiableAt ℝ (selectionEvaluation L.defect b) θ := by
  have h2 : selectionEvaluation L.defect b = fun θ => realRestriction (L.limitC b) θ + (0, b) :=
    funext (tori_eval_eq L hb)
  rw [h2]
  exact ((realRestriction_fderiv (tori_strip_pos d.strip_pos) (L.limit_holo b hb)
    (tori_isReal L hb) θ).1).add_const _

/-- Immersion bound: from the complex derivative bound `‖D(K - id)‖ ≤ 2⁻¹¹`. -/
theorem tori_immersion (hb : b ∈ L.Kinf) (θ v : SelectionR n) :
    (1 - (2 : ℝ)⁻¹ ^ 11) * ‖v‖ ≤ ‖fderiv ℝ (selectionEvaluation L.defect b) θ v‖ := by
  have hθ : selectionReal θ ∈ complexStrip n (d.strip / 4) :=
    fun i => by simpa [selectionReal] using tori_strip_pos d.strip_pos
  have hdd : DifferentiableAt ℂ (L.limitC b) (selectionReal θ) :=
    (L.limit_holo b hb).differentiableAt ((KAM.isOpen_complexStrip n _).mem_nhds hθ)
  have hi : HasFDerivAt (fun w : SelectionC n => ((w, 0) : SelectionPhaseC n))
      (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)) (selectionReal θ) :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const (0 : SelectionC n) _)
  have hg : fderiv ℂ (fun w => L.limitC b w - (w, 0)) (selectionReal θ) =
      fderiv ℂ (L.limitC b) (selectionReal θ) -
        ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) :=
    (hdd.hasFDerivAt.sub hi).fderiv
  have hbd := L.complex_derivative_bound b hb (selectionReal θ) hθ
  rw [hg] at hbd
  have h1 := (fderiv ℂ (L.limitC b) (selectionReal θ) -
    ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)).le_opNorm (selectionReal v)
  have hn : ‖realInclusion₂ n (fderiv ℝ (selectionEvaluation L.defect b) θ v)‖ =
      ‖fderiv ℝ (selectionEvaluation L.defect b) θ v‖ := norm_realInclusion₂ _
  have hvn : ‖selectionReal v‖ = ‖v‖ := norm_selectionReal v
  have hinl : ‖ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) (selectionReal v)‖ =
      ‖v‖ := by
    rw [norm_inl_apply, hvn]
  have htri : ‖ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) (selectionReal v)‖ ≤
      ‖fderiv ℂ (L.limitC b) (selectionReal θ) (selectionReal v)‖ +
      ‖(fderiv ℂ (L.limitC b) (selectionReal θ) -
        ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)) (selectionReal v)‖ := by
    have : ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) (selectionReal v) =
        fderiv ℂ (L.limitC b) (selectionReal θ) (selectionReal v) -
        (fderiv ℂ (L.limitC b) (selectionReal θ) -
          ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)) (selectionReal v) := by
      simp
    rw [this]
    exact norm_sub_le _ _
  rw [← hn, tori_fderiv_real L hb θ v]
  rw [hvn] at h1
  nlinarith [norm_nonneg v]

theorem tori_embedding (hb : b ∈ L.Kinf) (θ θ' : SelectionR n) :
    (1 - (2 : ℝ)⁻¹ ^ 11) * ‖θ - θ'‖ ≤
      ‖selectionEvaluation L.defect b θ - selectionEvaluation L.defect b θ'‖ := by
  have hl := L.angle_lipschitz b hb θ θ'
  have e : selectionEvaluation L.defect b θ - selectionEvaluation L.defect b θ' =
      (θ - θ', 0) + (L.defect b θ - L.defect b θ') := by
    unfold selectionEvaluation
    ext i <;> simp; ring
  have h0 : ‖((θ - θ', 0) : Phase n)‖ = ‖θ - θ'‖ := by simp [Prod.norm_def]
  have htri : ‖((θ - θ', 0) : Phase n)‖ ≤
      ‖selectionEvaluation L.defect b θ - selectionEvaluation L.defect b θ'‖ +
        ‖L.defect b θ - L.defect b θ'‖ := by
    have : ((θ - θ', 0) : Phase n) = (selectionEvaluation L.defect b θ -
        selectionEvaluation L.defect b θ') - (L.defect b θ - L.defect b θ') := by
      rw [e]; abel
    rw [this]
    exact norm_sub_le _ _
  nlinarith [norm_nonneg (θ - θ')]

section Lagrangian
variable (cx : WeakBudgetCtx d a)

include cx in
/-- Complex Lagrangian identity at real angles: the limit of the zero-section pullbacks. -/
theorem tori_lagrangian_C (hb : b ∈ L.Kinf) (θ : SelectionR n) (u v : SelectionC n) :
    Canonical.symplFormC (fderiv ℂ (L.limitC b) (selectionReal θ) u)
      (fderiv ℂ (L.limitC b) (selectionReal θ) v) = 0 := by
  have hstrip := cx.hyp.hstrip
  have hθ : selectionReal θ ∈ complexStrip n (d.strip / 4) :=
    fun i => by simpa [selectionReal] using tori_strip_pos d.strip_pos
  have hθ2 : selectionReal θ ∈ complexStrip n (a.strip / 2) :=
    selectionReal_mem_complexStrip (by linarith) θ
  have hdu := (L.derivative_uniform b hb).tendsto_at hθ
  have hu := ((ContinuousLinearMap.apply ℂ (SelectionPhaseC n) u).continuous.tendsto _).comp hdu
  have hv := ((ContinuousLinearMap.apply ℂ (SelectionPhaseC n) v).continuous.tendsto _).comp hdu
  have hΩ : Continuous (fun p : SelectionPhaseC n × SelectionPhaseC n =>
      Canonical.symplFormC p.1 p.2) := by
    unfold Canonical.symplFormC
    fun_prop
  have hlim := (hΩ.tendsto _).comp (hu.prodMk_nhds hv)
  have hzero : ∀ ν, Canonical.symplFormC
      ((fderiv ℂ (fun w => selectionCompose L.toSelectionChain (selectionReal b) ν (w, 0))
        (selectionReal θ)) u)
      ((fderiv ℂ (fun w => selectionCompose L.toSelectionChain (selectionReal b) ν (w, 0))
        (selectionReal θ)) v) = 0 := fun ν => by
    have h := selectionLim_stage_fderiv cx L.toSelectionComposition hb ν hθ2
    have e : ∀ w : SelectionC n,
        (fderiv ℂ (fun w => selectionCompose L.toSelectionChain (selectionReal b) ν (w, 0))
          (selectionReal θ)) w =
        fderiv ℂ (selectionCompose L.toSelectionChain (selectionReal b) ν)
          (selectionReal θ, 0) (w, 0) := fun w => by
      have := congrArg (fun T => T w) h
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at this
      exact this
    rw [e u, e v]
    rw [L.composition_symplectic ν ((selectionReal θ, 0), selectionReal b)
      (selectionLim_mem cx L.toSelectionComposition hb ν hθ2) (u, 0) (v, 0)]
    simp [Canonical.symplFormC]
  have h0 : Tendsto (fun ν => Canonical.symplFormC
      ((fderiv ℂ (fun w => selectionCompose L.toSelectionChain (selectionReal b) ν (w, 0))
        (selectionReal θ)) u)
      ((fderiv ℂ (fun w => selectionCompose L.toSelectionChain (selectionReal b) ν (w, 0))
        (selectionReal θ)) v)) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

include cx in
theorem tori_lagrangian (hb : b ∈ L.Kinf) (θ v w : SelectionR n) :
    symplecticForm (fderiv ℝ (selectionEvaluation L.defect b) θ v)
      (fderiv ℝ (selectionEvaluation L.defect b) θ w) = 0 := by
  have h := tori_lagrangian_C L cx hb θ (selectionReal v) (selectionReal w)
  rw [← tori_fderiv_real L hb θ v, ← tori_fderiv_real L hb θ w] at h
  set p := fderiv ℝ (selectionEvaluation L.defect b) θ v
  set q := fderiv ℝ (selectionEvaluation L.defect b) θ w
  have : Canonical.symplFormC (realInclusion₂ n p) (realInclusion₂ n q) =
      ((symplecticForm p q : ℝ) : ℂ) := by
    simp [Canonical.symplFormC, symplecticForm]
  rw [this] at h
  exact_mod_cast h

end Lagrangian

end Real

end KAM.Planetary

end
