/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Stopped
public import KAM.Nekhoroshev.Averaging.CompactMaximum

/-!
# Part N12: the good set (`bpN:p12:good`, `bpN:p12:bad`)

`avgGood h f R ε η K` is the set of `x ∈ K` whose flow exists on all of `[0, 1/ε]` and whose
displacement there has **strict** maximum `< η`. `good`: on a compact `K` it is relatively open
(the maximum over the compact time interval is continuous on the open set `avgOmega (1/ε)`), so its
complement in `K` is measurable. `bad` re-derives the stopped witness of `stopped` (for `f` itself)
and shows: the integral bound, the **nonstrict** threshold `η ≤ avgStopped` on the bad set for
`η ≤ R/8` (either the orbit exits the `R/8`-tube, or the maximum is `≥ η`), and the bound
`‖flow t x - x‖ ≤ avgStopped` on the good set at level `R/8` (strictness excludes an exit).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

def avgGood (h : (Fin n → ℂ) → ℂ) (f : AvgComplexPhase n → ℂ)
    (R ε η : ℝ) (K : Set (AvgPhase n)) : Set (AvgPhase n) :=
  {x ∈ K | x ∈ avgOmega h f R ε (1 / ε) ∧
    sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) < η}

section Aux

variable (d : AveragingData n R s h f) {ε : ℝ}
include d

theorem mem_flowDomain_of_omega {T : ℝ} {x : AvgPhase n} (hx : x ∈ avgOmega h f R ε T)
    {t : ℝ} (ht : t ∈ Icc 0 T) : (t, x) ∈ avgFlowDomain h f R ε := by
  have hmx := avgMaximal_spec d ε hx.1
  exact ⟨hx.1, (KAM.ODE.ordConnected_eIoo (avgTm h f R ε x) (avgTp h f R ε x)).out
    (KAM.ODE.zero_mem_eIoo hmx) hx.2 ht⟩

theorem continuousOn_disp (T : ℝ) :
    ContinuousOn (fun p : ℝ × AvgPhase n => ‖(avgFlow h f R ε p.1 p.2).2 - p.2.2‖)
      (Icc 0 T ×ˢ avgOmega h f R ε T) := by
  refine ((((continuousOn_avgFlow d ε).snd).sub
    (continuous_snd.snd.continuousOn)).norm).mono ?_
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  exact mem_flowDomain_of_omega d hx ht

theorem continuousOn_sSup_disp (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun x : AvgPhase n =>
      sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 T)) (avgOmega h f R ε T) :=
  compact_max_on hT (continuousOn_disp d T)

/-- On the orbit of a point with flow existing up to `T`, the displacement attains its maximum. -/
theorem exists_max_disp {T : ℝ} (hT : 0 ≤ T) {x : AvgPhase n} (hx : x ∈ avgOmega h f R ε T) :
    ∃ u ∈ Icc 0 T, sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 T) =
      ‖(avgFlow h f R ε u x).2 - x.2‖ := by
  have hc : ContinuousOn (fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) (Icc 0 T) := by
    have := (continuousOn_disp d T).comp (f := fun t : ℝ => (t, x))
      (by fun_prop) (fun t ht => ⟨ht, hx⟩)
    exact this
  obtain ⟨u, hu, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn
    (nonempty_Icc.2 hT) hc
  refine ⟨u, hu, le_antisymm (csSup_le ((nonempty_Icc.2 hT).image _) ?_) ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hmax ht
  · exact le_csSup ((isCompact_Icc.image_of_continuousOn hc).bddAbove) ⟨u, hu, rfl⟩

end Aux

section Main

/-- `bpN:p12:good`. -/
theorem good (d : AveragingData n R s h f) (K : Set (AvgPhase n)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    IsOpen {x : K | (x : AvgPhase n) ∈ avgGood h f R ε η K} ∧
    MeasurableSet (K \ avgGood h f R ε η K) := by
  have hT : (0 : ℝ) ≤ 1 / ε := by positivity
  set O : Set (AvgPhase n) := {x | x ∈ avgOmega h f R ε (1 / ε) ∧
    sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) < η} with hO
  have hOo : IsOpen O := by
    have := (continuousOn_sSup_disp d (1 / ε) hT).isOpen_inter_preimage
      (isOpen_avgOmega d ε (1 / ε)) (isOpen_Iio (a := η))
    exact this
  have hG : avgGood h f R ε η K = K ∩ O := rfl
  refine ⟨?_, ?_⟩
  · have : {x : K | (x : AvgPhase n) ∈ avgGood h f R ε η K} = Subtype.val ⁻¹' O := by
      ext x
      simp only [mem_ofPred_eq, hG, mem_inter_iff, mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [this]
    exact hOo.preimage continuous_subtype_val
  · have : K \ avgGood h f R ε η K = K \ O := by
      rw [hG]; ext x; simp only [mem_sdiff, mem_inter_iff]; tauto
    rw [this]
    exact hK.isClosed.measurableSet.diff hOo.measurableSet

/-- This helper re-derives the stopped witness; it does not assume a stopped bound. -/
theorem bad (d : AveragingData n R s h f) (K : Set (AvgPhase n)) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2)) :
    ∃ M₂ A₁ : ℝ, 0 ≤ M₂ ∧ 0 < A₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ x in K, avgStopped h f R s M₂ ε x) ≤ ENNReal.ofReal (A₁ * Real.sqrt ε) ∧
      (∀ η : ℝ, 0 < η → η ≤ R / 8 → ∀ x ∈ K \ avgGood h f R ε η K,
        ENNReal.ofReal η ≤ avgStopped h f R s M₂ ε x) ∧
      ∀ x ∈ avgGood h f R ε (R / 8) K, ∀ t ∈ Icc 0 (1 / ε),
        ENNReal.ofReal ‖(avgFlow h f R ε t x).2 - x.2‖ ≤ avgStopped h f R s M₂ ε x := by
  obtain ⟨M₂, A₁, hM0, hA, -, hst⟩ := stopped d K hK hKI
  refine ⟨M₂, A₁, hM0, hA, fun ε hε hε1 => ?_⟩
  obtain ⟨-, hint, hpt⟩ := hst f d.hf ε hε hε1
  have hT : (0 : ℝ) ≤ 1 / ε := by positivity
  have hR := d.hR
  -- an exit time before `1/ε` is a real number with displacement `R/8`
  have hexit : ∀ x ∈ K, avgTau h f R ε x < ((1 / ε : ℝ) : EReal) →
      ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 / ε ∧ ‖(avgFlow h f R ε τ x).2 - x.2‖ = R / 8 ∧
        (τ : EReal) = avgTau h f R ε x := by
    intro x hx hlt
    obtain ⟨hpos, -, -, hfin, -⟩ := exit d hε (hKI x hx)
    have hne : avgTau h f R ε x ≠ ⊤ := ne_top_of_lt hlt
    have hne' : avgTau h f R ε x ≠ ⊥ := ne_bot_of_gt hpos
    set τ := (avgTau h f R ε x).toReal with hτ
    have hcoe : (τ : EReal) = avgTau h f R ε x := EReal.coe_toReal hne hne'
    have hτ0 : 0 ≤ τ := by
      have : ((0 : ℝ) : EReal) ≤ (τ : EReal) := by rw [hcoe]; exact_mod_cast hpos.le
      exact_mod_cast this
    have hτT : τ ≤ 1 / ε := by
      have : (τ : EReal) ≤ ((1 / ε : ℝ) : EReal) := by rw [hcoe]; exact hlt.le
      exact_mod_cast this
    exact ⟨τ, hτ0, hτT, (hfin τ hcoe).2, hcoe⟩
  refine ⟨hint, ?_, ?_⟩
  · intro η hη hη8 x hx
    obtain ⟨hxK, hxn⟩ := hx
    by_cases hlt : avgTau h f R ε x < ((1 / ε : ℝ) : EReal)
    · obtain ⟨τ, hτ0, hτT, hτd, hτc⟩ := hexit x hxK hlt
      have := hpt x hxK τ hτ0 hτT hτc.le τ ⟨hτ0, le_rfl⟩
      rw [hτd] at this
      exact (ENNReal.ofReal_le_ofReal hη8).trans this
    · have hge : ((1 / ε : ℝ) : EReal) ≤ avgTau h f R ε x := not_lt.1 hlt
      obtain ⟨hltp, -⟩ := (exit d hε (hKI x hxK)).2.2.2.2.1 (1 / ε) hT hge
      have hmx := avgMaximal_spec d ε (show x ∈ avgDomain n R from
        ⟨mem_univ _, ball_subset_ball (by linarith) (hKI x hxK)⟩)
      have hΩ : x ∈ avgOmega h f R ε (1 / ε) := by
        refine ⟨⟨mem_univ _, ball_subset_ball (by linarith) (hKI x hxK)⟩, ?_, hltp⟩
        have h0 := (KAM.ODE.zero_mem_eIoo hmx).1
        exact h0.trans_le (by exact_mod_cast hT)
      obtain ⟨u, hu, hsup⟩ := exists_max_disp d hT hΩ
      have hsge : η ≤ sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) := by
        by_contra hlt'
        exact hxn ⟨hxK, hΩ, not_le.1 hlt'⟩
      rw [hsup] at hsge
      exact (ENNReal.ofReal_le_ofReal hsge).trans
        (hpt x hxK (1 / ε) hT le_rfl hge u hu)
  · intro x hx t ht
    obtain ⟨hxK, hΩ, hlt⟩ := hx
    have hge : ((1 / ε : ℝ) : EReal) ≤ avgTau h f R ε x := by
      by_contra hnot
      obtain ⟨τ, hτ0, hτT, hτd, -⟩ := hexit x hxK (not_le.1 hnot)
      have hbdd : BddAbove ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) := by
        have hc : ContinuousOn (fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) (Icc 0 (1 / ε)) :=
          (continuousOn_disp d (1 / ε)).comp (f := fun t : ℝ => (t, x))
            (by fun_prop) (fun t ht => ⟨ht, hΩ⟩)
        exact (isCompact_Icc.image_of_continuousOn hc).bddAbove
      have : ‖(avgFlow h f R ε τ x).2 - x.2‖ ≤
          sSup ((fun t => ‖(avgFlow h f R ε t x).2 - x.2‖) '' Icc 0 (1 / ε)) :=
        le_csSup hbdd ⟨τ, ⟨hτ0, hτT⟩, rfl⟩
      rw [hτd] at this
      linarith
    exact hpt x hxK (1 / ε) hT le_rfl hge t ht

end Main

end KAM.Nekhoroshev

end
