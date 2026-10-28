/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Selection

/-! # P11B selection at a general admissible schedule

`parameter_selection` is stated at `adm_params d ε`, but the composition export needs the output
record `SelectionOutput` at the ε-adapted schedule. The proofs of `parameter_selection` use the
schedule only through its admissibility, so they are repeated here at `selectionSchedGen d s₀ ε₀`
(the schedule of `selectionAdapted`), taking the iteration as an argument.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Main

/-- Every stage of the fixed cutoff family is smooth near `K` and agrees with `Re ω_j` on `K_j`. -/
theorem selection_stage_all_gen (d : SelectionData n) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (c : SelectionChain n)
    (hc : ∀ ν, SelectionExtensionChain d (selectionSchedGen d s₀ ε₀) c ν)
    (χ : ℕ → SelectionR n → ℝ) (hχ : SelectionCutoffSpec d (selectionSchedGen d s₀ ε₀) c χ)
    (j : ℕ) :
    ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j) (selectionV d) ∧
      (∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
        selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      ∀ i ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector i (selectionExtendedFrequency d c χ j - frequencyMap d.h) y ≤
          selectionThetaMax d :=
  selection_stage_close_gen d s₀ ε₀ hA hs he0 c j (hc j) χ (fun i _ => hχ i) le_rfl

/-- The finite tests for the fixed cutoff family: compact, retained, and of large measure. -/
theorem selection_tests_gen (d : SelectionData n) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (c : SelectionChain n)
    (hc : ∀ ν, SelectionFiniteChain d (selectionSchedGen d s₀ ε₀) c ν)
    (χ : ℕ → SelectionR n → ℝ) (hχ : SelectionCutoffSpec d (selectionSchedGen d s₀ ε₀) c χ)
    (ν : ℕ) :
    IsCompact (selectionFiniteTests d (selectionSchedGen d s₀ ε₀) c χ ν) ∧
      selectionFiniteTests d (selectionSchedGen d s₀ ε₀) c χ ν ⊆
        selectionRetained (selectionSchedGen d s₀ ε₀) d c ν ∧
      volume d.K - ENNReal.ofReal d.loss ≤
        volume (selectionFiniteTests d (selectionSchedGen d s₀ ε₀) c χ ν) := by
  obtain ⟨hA, ht1, hs, he0⟩ := selection_adm_facts d ε he hsmall
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have ht1 : (selectionSchedGen d s₀ ε₀).t₀ ≤ 1 :=
    (hA.t_le.trans (div_le_self d.theta_pos.le hsq)).trans d.theta_le
  set a := selectionSchedGen d s₀ ε₀ with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  have hstage := fun j => selection_stage_all_gen d s₀ ε₀ hA hs he0 c
    (fun ν => (hc ν).toSelectionExtensionChain) χ hχ j
  have hext : ∀ j, ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
      selectionRe (selectionFrequency d c j (selectionReal b)) := fun j => (hstage j).2.1
  set wt : (Fin n → ℤ) → SelectionR n → SelectionR n :=
    fun k => selectionExtendedFrequency d c χ (min (selectionModeStage a k) ν) with hwt
  have hG := selection_family_measure d wt (fun k _ => (hstage _).1)
    (fun k _ j hj y hy => (hstage _).2.2 j hj y hy)
  set Hs := selectionFiniteTests d a c χ ν with hHs
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
      (fun k => (hstage _).1.continuousOn.mono hKV) _ _
  exact ⟨hcomp, fun b hb => selection_retained_of_tests d a c ν (hc ν) hT χ
    (fun j _ => hext j) hb.1 hb.2, hG.trans (measure_mono hGH)⟩


theorem selection_output_gen (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (o : SelectionIteration d f (selectionSchedGen d s₀ ε₀)) :
    Nonempty (SelectionOutput d f (selectionSchedGen d s₀ ε₀)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have ht1 : (selectionSchedGen d s₀ ε₀).t₀ ≤ 1 :=
    (hA.t_le.trans (div_le_self d.theta_pos.le hsq)).trans d.theta_le
  set a := selectionSchedGen d s₀ ε₀ with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  have cx : WeakBudgetCtx d a := weakBudgetCtx_of d a hA rfl rfl rfl rfl rfl rfl hs he0
  obtain ⟨χ, hχ⟩ := selection_all_cutoffs d a o.toSelectionChain
    (fun ν => (o.chain ν).toSelectionExtensionChain) hA.t_pos ht1 d.tau_nonneg
  obtain ⟨ωstar, hstar, hSω, hSh, hUω, hUh, hωs, hhs, hCω, hCh, hTω, hTh⟩ :=
    selection_limit_series cx o
  have htests := selection_tests_gen d s₀ ε₀ hA hs he0 o.toSelectionChain o.chain χ hχ
  have hstage := selection_stage_all_gen d s₀ ε₀ hA hs he0 o.toSelectionChain
    (fun ν => (o.chain ν).toSelectionExtensionChain) χ hχ
  set Hfin := selectionFiniteTests d a o.toSelectionChain χ with hHfin
  set Hinf : Set (SelectionR n) := {b ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * selectionExtendedFrequency d o.toSelectionChain χ
        (selectionModeStage a k) b i|} with hHinf
  have hmono : Antitone Hfin := fun ν ν' hνν' b hb =>
    ⟨hb.1, fun k hk hkT => hb.2 k hk (hkT.trans (by
      unfold selectionT
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hνν') (by linarith)))⟩
  have hHeq : Hinf = ⋂ ν, Hfin ν := by
    ext b
    simp only [mem_iInter]
    constructor
    · rintro ⟨hb, h⟩ ν
      exact ⟨hb, fun k hk _ => h k fun h0 => by simp [h0, selectionModeLength] at hk⟩
    · intro h
      refine ⟨(h 0).1, fun k hk => ?_⟩
      obtain ⟨ν, hν⟩ := selectionT_unbounded a hT (selectionModeLength k)
      exact (h ν).2 k (selectionModeLength_pos hk) hν
  have hKd : ∀ j, o.K j ⊆ d.K := fun j => by
    have := selectionChain_antitone (o.chain j).toSelectionExtensionChain (j := 0) j (by omega)
    rw [zero_add, (o.chain j).initial] at this
    exact this
  have hHsub : Hinf ⊆ ⋂ j, o.K j := by
    intro b hb
    rw [hHeq] at hb
    simp only [mem_iInter] at hb ⊢
    intro j
    cases j with
    | zero => rw [(o.chain 0).initial]; exact (hb 0).1
    | succ ν =>
      rw [(o.chain (ν + 1)).retained ν (by omega)]
      exact (htests ν).2.1 (hb ν)
  have hcompH : ∀ ν, IsCompact (Hfin ν) := fun ν => (htests ν).1
  have hcompKinf : IsCompact (⋂ j, o.K j) :=
    ((o.chain 0).compact 0 le_rfl).of_isClosed_subset
      (isClosed_iInter fun j => ((o.chain j).compact j le_rfl).isClosed) (iInter_subset _ 0)
  have hcompHinf : IsCompact Hinf := by
    rw [hHeq]
    exact (hcompH 0).of_isClosed_subset (isClosed_iInter fun ν => (hcompH ν).isClosed)
      (iInter_subset _ 0)
  have hmeas : volume d.K - ENNReal.ofReal d.loss ≤ volume Hinf := by
    rw [hHeq]
    have hlim := tendsto_measure_iInter_atTop (μ := volume) (s := Hfin)
      (fun ν => (hcompH ν).isClosed.measurableSet.nullMeasurableSet) hmono
      ⟨0, (hcompH 0).measure_lt_top.ne⟩
    exact ge_of_tendsto' hlim fun ν => (htests ν).2.2
  have hγ : 0 < a.γ := selectionGamma_pos d
  have hdio : ∀ b ∈ Hinf, IsDiophantine a.γ a.τ (ωstar b) := by
    intro b hb k hk
    have hbK : b ∈ ⋂ j, o.K j := hHsub hb
    have hL := selectionModeLength_pos hk
    set m := selectionModeStage a k with hm
    have hbm : b ∈ o.K m := mem_iInter.1 hbK m
    have hext := (hstage m).2.1 b hbm
    have htail := hTω m b hbK
    have hLT : selectionModeLength k ≤ selectionT a m :=
      (selectionModeStage_mem_shell a hT hL).2.1
    have hpow : a.γ * selectionT a m ^ (-a.τ - 1) ≤
        a.γ * selectionModeLength k ^ (-a.τ - 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL hLT
        (by linarith [cx.hyp.hτ])) hγ.le
    have e : 2 * a.γ * KAM.Fourier.modeSize k ^ (-a.τ) =
        2 * a.γ / selectionModeLength k ^ a.τ := by
      rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), div_eq_mul_inv]
      rfl
    have hu : 2 * a.γ * KAM.Fourier.modeSize k ^ (-a.τ) ≤
        |p11dotZ k (selectionExtendedFrequency d o.toSelectionChain χ m b)| := by
      rw [e]
      exact hb.2 k hk
    have ht : ‖selectionExtendedFrequency d o.toSelectionChain χ m b - ωstar b‖ ≤
        a.γ * KAM.Fourier.modeSize k ^ (-a.τ - 1) := by
      rw [norm_sub_rev, hext]
      exact htail.trans (((iter_tail cx m).2).trans hpow)
    have hbr := limit_bridge (m := n) hγ hk hu ht
    rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), ← div_eq_mul_inv] at hbr
    exact hbr
  exact ⟨{ toSelectionIteration := o
           cutoffs := χ
           cutoff_spec := fun j => ⟨(hχ j).1, (hχ j).2.1, (hχ j).2.2.1, (hχ j).2.2.2.1⟩
           extended := selectionExtendedFrequency d o.toSelectionChain χ
           extended_formula := fun _ => rfl
           extended_regular := fun j => (hstage j).1
           extended_eq := fun j => (hstage j).2.1
           Kinf := ⋂ j, o.K j
           Hinf := Hinf
           Kinf_eq := rfl
           compact_K := hcompKinf
           compact_H := hcompHinf
           H_subset := hHsub
           modeStage := selectionModeStage a
           modeStage_eq := rfl
           modeStage_spec := fun k hk =>
             selectionModeStage_mem_shell a hT (selectionModeLength_pos hk)
           Hinf_eq := rfl
           finite_compact := fun ν => (htests ν).1
           finite_inclusion := fun ν b hb => by
             rw [(o.chain (ν + 1)).retained ν (by omega)]
             exact (htests ν).2.1 hb
           finite_measure := fun ν => (htests ν).2.2
           measure_H := hmeas
           ωstar := ωstar
           hstar := hstar
           frequency_summable := hSω
           energy_summable := hSh
           frequency_uniform := hUω
           energy_uniform := hUh
           ωstar_sum := hωs
           hstar_sum := hhs
           ωstar_cont := hCω
           hstar_cont := hCh
           frequency_tail := hTω
           energy_tail := hTh
           diophantine := hdio }⟩

end Main

end KAM.Planetary

end
