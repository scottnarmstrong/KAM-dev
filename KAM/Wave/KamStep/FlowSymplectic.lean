/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowVariational
public import KAM.Wave.KamStep.SymplecticFlow

/-!
# Symplecticity of the flow (`bpW:w5:flow-calc` (ii), steps `c-var`, `c-symp`)

For `h : FlowHyp X V U M δ`, a bounded bilinear form `B` skewed by every `DX(z)`, `z ∈ V`
(step `c-skew`), is preserved by `Dφ^t(w)` for `w ∈ U` (`holoFlow_preserves_form`): the curve
`a(t) = Dφ^t(w) W` solves `a' = DX(φ^t w) a` (`hasDerivWithinAt_fderiv_holoFlow`) and
`stepSymp_const` applies.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

theorem continuousOn_flowVarG {w : F} (hw : w ∈ U) :
    ContinuousOn (flowVarG X w) (Icc (-1 : ℝ) 1) :=
  ((continuousOn_fderiv_of_holomorphic h.isOpen_V h.holo).comp (continuousOn_holoFlow_time h hw)
    fun _ hσ => h.mem_V_of_ball hw (holoFlow_mem_ball h hw hσ)).clm_comp
    (continuousOn_fderiv_holoFlow_time h hw)

/-- The variational curve `a(t) = Dφ^t(w) W` has derivative `DX(φ^t w) a(t)`. -/
theorem hasDerivWithinAt_fderiv_holoFlow {w : F} (hw : w ∈ U) (W : F) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (fun s => fderiv ℂ (holoFlow X s) w W)
      (fderiv ℂ X (holoFlow X t w) (fderiv ℂ (holoFlow X t) w W)) (Icc (-1) 1) t := by
  set q : ℝ → ℝ := fun σ => max (-1) (min 1 σ) with hqdef
  have hq : Continuous q := by fun_prop
  have hqI : ∀ σ ∈ Icc (-1 : ℝ) 1, q σ = σ := fun σ hσ => by
    simp [q, min_eq_right hσ.2, max_eq_right hσ.1]
  have hqmem : ∀ σ, q σ ∈ Icc (-1 : ℝ) 1 := fun σ =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  set g : ℝ → F := fun σ => flowVarG X w (q σ) W with hgdef
  have hg : Continuous g := by
    have : ContinuousOn (fun σ => flowVarG X w σ W) (Icc (-1 : ℝ) 1) :=
      (ContinuousLinearMap.apply ℂ F W).continuous.comp_continuousOn (continuousOn_flowVarG h hw)
    exact this.comp_continuous hq hqmem
  have hgt : g t = fderiv ℂ X (holoFlow X t w) (fderiv ℂ (holoFlow X t) w W) := by
    simp [g, hqI t ht, flowVarG]
  have key : HasDerivAt (fun u => W + ∫ σ in (0 : ℝ)..u, g σ) (g t) t :=
    (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add W
  have hrep : ∀ s ∈ Icc (-1 : ℝ) 1,
      fderiv ℂ (holoFlow X s) w W = W + ∫ σ in (0 : ℝ)..s, g σ := by
    intro s hs
    have hsub : uIcc 0 s ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hs
    have hint : IntervalIntegrable (flowVarG X w) volume 0 s :=
      (intervalIntegrable_flowVarG h hw).mono_set (by
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact hsub)
    rw [fderiv_holoFlow_eq h hw hs]
    have := ((ContinuousLinearMap.apply ℂ F W).restrictScalars ℝ).intervalIntegral_comp_comm hint
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply] at this
    rw [add_apply, ContinuousLinearMap.id_apply, ← this]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    show flowVarG X w σ W = flowVarG X w (q σ) W
    rw [hqI σ (hsub hσ)]
  rw [← hgt]
  exact key.hasDerivWithinAt.congr (fun s hs => hrep s hs) (hrep t ht)

/-- **Symplecticity of the flow** (`bpW:w5:flow-calc` (ii)): a bounded bilinear form skewed by
every `DX(z)` on `V` is preserved by `Dφ^t(w)`, `w ∈ U`. -/
theorem holoFlow_preserves_form (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hskew : ∀ z ∈ V, ∀ x y, B (fderiv ℂ X z x) y + B x (fderiv ℂ X z y) = 0) {w : F}
    (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (W W' : F) :
    B (fderiv ℂ (holoFlow X t) w W) (fderiv ℂ (holoFlow X t) w W') = B W W' := by
  have h0 : fderiv ℂ (holoFlow X 0) w = ContinuousLinearMap.id ℂ F := by
    rw [fderiv_holoFlow_eq h hw ⟨by norm_num, by norm_num⟩]; simp
  have := stepSymp_const B (a := fun s => fderiv ℂ (holoFlow X s) w W)
    (b := fun s => fderiv ℂ (holoFlow X s) w W') (K := fun s => fderiv ℂ X (holoFlow X s w))
    (fun s hs x y => hskew _ (h.mem_V_of_ball hw (holoFlow_mem_ball h hw hs)) x y)
    (fun s hs => hasDerivWithinAt_fderiv_holoFlow h hw W hs)
    (fun s hs => hasDerivWithinAt_fderiv_holoFlow h hw W' hs) ht
  simpa [h0] using this

end KAM.Wave
