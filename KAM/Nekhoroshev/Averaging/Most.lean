/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.GoodSet
public import KAM.Nekhoroshev.Averaging.FlowRegular

/-!
# Part N12: the "most" averaging statement (`bpN:p12:s-most#data`, `mo-E`, `mo-z`)

`averaging_most_core`: for good data on a compact `K` with actions in `B(0, R/2)`, the exceptional
set is `E = K \ avgGood h f R ε η K`. By `good` it is measurable, and by `bad` and Markov's
inequality its volume is at most `A₁ √ε / η`. For `x ∈ K \ E` the solution `z t = avgFlow … t x`
is a solution on all of `[0, 1/ε]` (the closed interval lies in the maximal open interval), with
displacement `≤ sSup < η`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

theorem averaging_most_core (d : AveragingData n R s h f) (K : Set (AvgPhase n))
    (hK : IsCompact K) (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ η : ℝ, 0 < η → η ≤ R / 8 →
      ∃ E : Set (AvgPhase n), MeasurableSet E ∧ E ⊆ K ∧
        volume E ≤ ENNReal.ofReal (A * Real.sqrt ε / η) ∧ ∀ x ∈ K \ E,
        ∃ z : ℝ → AvgPhase n, z 0 = x ∧ IsSolutionOn (avgH h f ε)
          (actionBall n R) (Icc 0 (1 / ε)) z ∧
          ∀ t ∈ Icc 0 (1 / ε), ‖(z t).2 - x.2‖ ≤ η := by
  obtain ⟨M₂, A₁, hM0, hA, hbad⟩ := bad d K hK hKI
  refine ⟨A₁, hA, fun ε hε hε1 η hη hη8 => ?_⟩
  obtain ⟨hint, hex, -⟩ := hbad ε hε hε1
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hT : (0 : ℝ) ≤ 1 / ε := by positivity
  refine ⟨K \ avgGood h f R ε η K, (good d K hK hε η).2, sdiff_subset, ?_, ?_⟩
  · -- Markov for the (Borel) extension of `avgStopped`
    set g := avgStoppedExt h f R s M₂ ε with hg
    have hgm : Measurable g := measurable_avgStoppedExt d ε M₂ hε hM0
    have hηne : ENNReal.ofReal η ≠ 0 := by simpa using hη
    have hMk := meas_ge_le_lintegral_div (μ := volume.restrict K) hgm.aemeasurable hηne
      ENNReal.ofReal_ne_top
    have hsub : K \ avgGood h f R ε η K ⊆ {x | ENNReal.ofReal η ≤ g x} := by
      intro x hx
      show ENNReal.ofReal η ≤ avgStoppedExt h f R s M₂ ε x
      rw [← avgStopped_eq_ext d ε M₂ hε (hKI x hx.1)]
      exact hex η hη hη8 x hx
    have hE : volume (K \ avgGood h f R ε η K) ≤
        (∫⁻ a in K, g a) / ENNReal.ofReal η := by
      calc volume (K \ avgGood h f R ε η K)
          = (volume.restrict K) (K \ avgGood h f R ε η K) := by
            rw [Measure.restrict_apply' hKm, inter_eq_left.2 sdiff_subset]
        _ ≤ (volume.restrict K) {x | ENNReal.ofReal η ≤ g x} := measure_mono hsub
        _ ≤ _ := hMk
    have hint' : (∫⁻ a in K, g a) ≤ ENNReal.ofReal (A₁ * Real.sqrt ε) := by
      refine le_trans (le_of_eq (setLIntegral_congr_fun hKm fun x hx => ?_)) hint
      rw [hg, ← avgStopped_eq_ext d ε M₂ hε (hKI x hx)]
    refine hE.trans ?_
    rw [ENNReal.ofReal_div_of_pos hη]
    exact ENNReal.div_le_div_right hint' _
  · intro x hx
    obtain ⟨hxK, hxn⟩ := hx
    have hxg : x ∈ avgGood h f R ε η K := by
      by_contra hno; exact hxn ⟨hxK, hno⟩
    obtain ⟨-, hΩ, hlt⟩ := hxg
    have hxD : x ∈ avgDomain n R := hΩ.1
    have hmx := avgMaximal_spec d ε hxD
    have hred := (KAM.ODE.ham_reduction (isOpen_univ.prod isOpen_ball)
      (avgDomain_subset_Wdom d) (avgH_contDiffOn d ε)).2 (Icc 0 (1 / ε))
      (fun t => avgFlow h f R ε t x)
    refine ⟨fun t => avgFlow h f R ε t x, hmx.init, hred.1.2 ?_, fun t ht => ?_⟩
    · refine hmx.isSolution.mono ?_
      intro t ht
      exact (mem_flowDomain_of_omega d hΩ ht).2
    · have hbdd : BddAbove ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) := by
        have hc : ContinuousOn (fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) (Icc 0 (1 / ε)) :=
          (continuousOn_disp d (1 / ε)).comp (f := fun t : ℝ => (t, x))
            (by fun_prop) (fun t ht => ⟨ht, hΩ⟩)
        exact (isCompact_Icc.image_of_continuousOn hc).bddAbove
      exact (le_csSup hbdd ⟨t, ht, rfl⟩).trans hlt.le

end KAM.Nekhoroshev

end
