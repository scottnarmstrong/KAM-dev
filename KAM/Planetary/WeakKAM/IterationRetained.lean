/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.FiniteMeasure
public import KAM.Planetary.WeakKAM.IterationFacts
public import KAM.Planetary.WeakKAM.IterationAux

/-! # P11B iteration: the retained set at an arbitrary admissible radius

`finite_measure` of the finite-measure package is stated at `adm_params d ε`. The inductive lemma
is also needed at the adapted radius, so the same proof is repeated for the schedule
`selectionSchedGen d s₀ ε₀` with free `s₀`, `ε₀` and the admissibility hypothesis `A1`–`A6`.
The retained set of a finite chain is compact and (by the measure estimate) nonempty.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology Pointwise
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ}

/-- `stepP:p11a:fm-close`: every stage `j ≤ ν` is smooth, agrees with `ω_j` on `K_j`, and stays
`θ_max`-close to `ω`. -/
theorem selection_stage_close_gen (d : SelectionData n) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (c : SelectionChain n) (ν : ℕ)
    (hc : SelectionExtensionChain d (selectionSchedGen d s₀ ε₀) c ν) (χ : ℕ → SelectionR n → ℝ)
    (hχ : ∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
      (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
      tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤
        selectiont (selectionSchedGen d s₀ ε₀) j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k (χ j) y a'| ≤
          selectionCutoffC n d.μ k * (4 / selectiont (selectionSchedGen d s₀ ε₀) j) ^ k)
    {j : ℕ} (hj : j ≤ ν) :
    ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j) (selectionV d) ∧
      (∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
        selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      ∀ i ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector i (selectionExtendedFrequency d c χ j - frequencyMap d.h) y ≤
          selectionThetaMax d := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have ht1 : (selectionSchedGen d s₀ ε₀).t₀ ≤ 1 :=
    (hA.t_le.trans (div_le_self d.theta_pos.le hsq)).trans d.theta_le
  set a := selectionSchedGen d s₀ ε₀ with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  obtain ⟨h1, h2, h3⟩ := selection_stage_of_cutoffs d a c j (hc.mono hj) hA.t_pos ht1
    d.tau_nonneg χ fun i hi => hχ i (lt_of_lt_of_le hi hj)
  refine ⟨h1, h2, fun i hi y hy => (h3 i hi y hy).trans ?_⟩
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hγ : 0 < a.γ := selectionGamma_pos d
  have hcol := hA.collar
  have hinc := hA.increment
  have hlam : 0 ≤ a.ε₀ / a.s₀ := div_nonneg he0.le hs.le
  have hprops := schedule_props (C₁ := d.C₁) a d.n_pos d.μ_pos d.tau_nonneg hγ hT hA.t_pos hs
    he0 d.strip_pos d.hessian_normalized (by nlinarith [mul_pos hC hA.t_pos]) hinc hcol j 0
  have hsum := hprops.2.2.2.2.2.2.2.2.2.2.1
  have hE := selectionExtensionC_pos d.n_pos d.μ
  have hsum' : ∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ d.μ ≤
      4 * (a.ε₀ / a.s₀) / a.t₀ ^ d.μ := hsum
  calc selectionExtensionC n d.μ * ∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ d.μ
      ≤ selectionExtensionC n d.μ * (4 * (a.ε₀ / a.s₀) / a.t₀ ^ d.μ) :=
        mul_le_mul_of_nonneg_left hsum' hE.le
    _ = 4 * selectionExtensionC n d.μ * (a.ε₀ / a.s₀) / a.t₀ ^ d.μ := by ring
    _ ≤ selectionThetaMax d := hA.closeness


/-- Full finite-stage measure lemma; extensions are outputs, never a supplied good family. -/
theorem finite_measure_gen (d : SelectionData n) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (c : SelectionChain n) (ν : ℕ)
    (hc : SelectionFiniteChain d (selectionSchedGen d s₀ ε₀) c ν) :
    ∃ χ : ℕ → SelectionR n → ℝ,
      (∀ j ≤ ν, ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j)
        {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
        ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
          selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      let a := selectionSchedGen d s₀ ε₀
      let H := {b ∈ d.K | ∀ k : Fin n → ℤ,
        0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
        2 * a.γ / selectionModeLength k ^ a.τ ≤
          |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|}
      IsCompact H ∧ H ⊆ selectionRetained a d c ν ∧
        volume d.K - ENNReal.ofReal d.loss ≤ volume H ∧ H.Nonempty := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have ht1 : (selectionSchedGen d s₀ ε₀).t₀ ≤ 1 :=
    (hA.t_le.trans (div_le_self d.theta_pos.le hsq)).trans d.theta_le
  set a := selectionSchedGen d s₀ ε₀ with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  obtain ⟨χ, hχ⟩ := selection_coherent_cutoffs d a c ν hc.toSelectionExtensionChain hA.t_pos ht1
    d.tau_nonneg
  have hstage := fun (j : ℕ) (hj : j ≤ ν) =>
    selection_stage_close_gen d s₀ ε₀ hA hs he0 c ν hc.toSelectionExtensionChain χ hχ hj
  have hext : ∀ j ≤ ν, ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
      selectionRe (selectionFrequency d c j (selectionReal b)) := fun j hj => (hstage j hj).2.1
  set wt : (Fin n → ℤ) → SelectionR n → SelectionR n :=
    fun k => selectionExtendedFrequency d c χ (min (selectionModeStage a k) ν) with hwt
  have hG := selection_family_measure d wt (fun k _ => (hstage _ (min_le_right _ _)).1)
    (fun k _ j hj y hy => (hstage _ (min_le_right _ _)).2.2 j hj y hy)
  set Hs := {b ∈ d.K | ∀ k : Fin n → ℤ,
        0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
        2 * a.γ / selectionModeLength k ^ a.τ ≤
          |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|}
    with hHs
  have hGH : {y ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
      2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) ≤ |p11dotZ k (wt k y)|} ⊆ Hs := by
    rintro b ⟨hbK, hb⟩
    refine ⟨hbK, fun k hk hkT => ?_⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp [selectionModeLength] at hk
    have h1 := hb k hk0
    have hst : selectionModeStage a k ≤ ν := selectionModeStage_le a hT hk hkT
    simp only [wt, min_eq_left hst] at h1
    have e : 2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) =
        2 * a.γ / selectionModeLength k ^ a.τ := by
      rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), div_eq_mul_inv]
      rfl
    rw [← e]
    exact h1
  have hKV : d.K ⊆ selectionV d := fun x hx =>
    selectionThick_subset_V d (K_subset_selectionThick d.K d.theta_pos.le hx)
  have hHeq : Hs = {b ∈ d.K | ∀ k : Fin n → ℤ, 0 < selectionModeLength k →
      selectionModeLength k ≤ selectionT a ν → 2 * a.γ / selectionModeLength k ^ a.τ ≤
        |∑ i, (k i : ℝ) * wt k b i|} := by
    ext b
    refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
      forall_congr' fun hkT => ?_
    simp only [wt, min_eq_left (selectionModeStage_le a hT hk hkT)]
  have hcomp : IsCompact Hs := by
    rw [hHeq]
    exact isCompact_selection_tests d.compact wt
      (fun k => (hstage _ (min_le_right _ _)).1.continuousOn.mono hKV) _ _
  have hmeas : volume d.K - ENNReal.ofReal d.loss ≤ volume Hs := hG.trans (measure_mono hGH)
  have hne : Hs.Nonempty := by
    refine nonempty_of_measure_ne_zero (μ := volume) ?_
    intro h0
    rw [h0, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at hmeas
    exact absurd d.loss_lt (not_lt.2 hmeas)
  refine ⟨χ, fun j hj => ⟨(hstage j hj).1, (hstage j hj).2.1⟩, ?_⟩
  exact ⟨hcomp, fun b hb => selection_retained_of_tests d a c ν hc hT χ hext hb.1 hb.2, hmeas,
    hne⟩


theorem selectionRetained_nonempty (d : SelectionData n) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    {ch : SelectionChain n} {ν : ℕ}
    (hc : SelectionFiniteChain d (selectionSchedGen d s₀ ε₀) ch ν) :
    (selectionRetained (selectionSchedGen d s₀ ε₀) d ch ν).Nonempty := by
  obtain ⟨χ, -, hcomp, hsub, -, ⟨b, hb⟩⟩ := finite_measure_gen d s₀ ε₀ hA hs he0 ch ν hc
  exact ⟨b, hsub hb⟩

/-- The retained set of a finite chain is compact: a closed subset of `K_ν`. -/
theorem selectionRetained_isCompact {d : SelectionData n} {a : SelectionSchedule n}
    (c : WeakBudgetCtx d a) {ch : SelectionChain n} {ν : ℕ}
    (hc : SelectionExtensionChain d a ch ν) : IsCompact (selectionRetained a d ch ν) := by
  have hK := hc.compact ν le_rfl
  have hcont : ContinuousOn (fun b => selectionFrequency d ch ν (selectionReal b)) (ch.K ν) := by
    refine (selection_frequency_differentiableOn c hc).continuousOn.comp
      continuous_selectionReal.continuousOn fun b hb => ?_
    refine ⟨b, hb, ?_⟩
    have : (selectionReal b - fun i => ((b i : ℝ) : ℂ)) = 0 := by
      funext i; simp [selectionReal]
    rw [this]
    simpa using wbud_t_pos c ν
  set S : Set (Fin n → ℤ) := selectionShell a ν with hS
  have hg : ∀ k : Fin n → ℤ, ContinuousOn (fun b => ‖∑ i, (k i : ℂ) * selectionFrequency d ch ν
      (selectionReal b) i‖) (ch.K ν) := fun k =>
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul
      ((continuous_apply i).comp_continuousOn hcont)).norm
  have hcl : IsClosed (ch.K ν ∩ ⋂ k ∈ S, (ch.K ν ∩ (fun b => ‖∑ i, (k i : ℂ) *
      selectionFrequency d ch ν (selectionReal b) i‖) ⁻¹'
        Ici (2 * a.γ / selectionModeLength k ^ a.τ))) :=
    hK.isClosed.inter (isClosed_biInter fun k _ =>
      (hg k).preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
  refine hK.of_isClosed_subset ?_ (fun b hb => hb.1)
  convert hcl using 1
  ext b
  simp only [selectionRetained, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_Ici,
    hS]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun k hk => ⟨hb, h k hk⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun k hk => (h k hk).2⟩

end KAM.Planetary

end
