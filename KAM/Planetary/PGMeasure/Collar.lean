/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PG.Setting

/-!
# P Parts 4-5: the boundary collar (`bpP:p4:collar`, `bpP:p4:domain-collar`)

The frontier crossing `ext_conn`, the collar lemma `collar` for the inner core of a bounded open
set, the product-neighbourhood identity `realNbhd_joinedActions` (max norm) and the unnormalised
enlargement estimate `domain_collar_helper`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-CO.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

theorem ext_conn {C V : Set (Fin a → ℝ)} (hC : IsPreconnected C)
    (hCV : (C ∩ V).Nonempty) (hCc : (C \ V).Nonempty) : (C ∩ frontier V).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hfr : ∀ x ∈ C, x ∉ frontier V := fun x hx hf => by
    have : x ∈ C ∩ frontier V := ⟨hx, hf⟩
    rw [hne] at this
    exact this
  obtain ⟨x, hxC, hxV⟩ := hCV
  obtain ⟨y, hyC, hyV⟩ := hCc
  have hx : x ∈ interior V := by
    by_contra h
    exact hfr x hxC ⟨subset_closure hxV, h⟩
  have hy : y ∈ (closure V)ᶜ := by
    intro h
    exact hfr y hyC ⟨h, fun h' => hyV (interior_subset h')⟩
  have hcov : C ⊆ interior V ∪ (closure V)ᶜ := by
    intro z hz
    by_cases h : z ∈ closure V
    · left
      by_contra h'
      exact hfr z hz ⟨h, h'⟩
    · right
      exact h
  obtain ⟨z, _, hz1, hz2⟩ := hC _ _ isOpen_interior isClosed_closure.isOpen_compl hcov ⟨x, hxC, hx⟩
    ⟨y, hyC, hy⟩
  exact hz2 (subset_closure (interior_subset hz1))

theorem realNbhd_joinedActions (X : Set (Fin a → ℝ)) (Y : Set (Fin b → ℝ)) (s : ℝ) :
    realNbhd (joinedActions X Y) s = joinedActions (realNbhd X s) (realNbhd Y s) := by
  ext x
  simp only [realNbhd, joinedActions, mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hyX, hyY⟩, hd⟩
    have hs : 0 < s := lt_of_le_of_lt dist_nonneg hd
    rw [dist_pi_lt_iff hs] at hd
    refine ⟨⟨blockFast y, hyX, ?_⟩, ⟨blockSlow y, hyY, ?_⟩⟩
    · rw [dist_pi_lt_iff hs]
      exact fun i => hd _
    · rw [dist_pi_lt_iff hs]
      exact fun i => hd _
  · rintro ⟨⟨y₁, hy₁, h₁⟩, ⟨y₂, hy₂, h₂⟩⟩
    have hs : 0 < s := lt_of_le_of_lt dist_nonneg h₁
    rw [dist_pi_lt_iff hs] at h₁ h₂
    refine ⟨Fin.append y₁ y₂, ⟨?_, ?_⟩, ?_⟩
    · have : blockFast (Fin.append y₁ y₂) = y₁ := funext fun i => by simp [blockFast]
      rwa [this]
    · have : blockSlow (Fin.append y₁ y₂) = y₂ := funext fun i => by simp [blockSlow]
      rwa [this]
    · rw [dist_pi_lt_iff hs]
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa [blockFast] using h₁ j
      · simpa [blockSlow] using h₂ j

/-- The splitting of a block vector into its fast and slow parts, as a measurable equivalence. -/
def blockSplitEquiv (a b : ℕ) : (Fin (a+b) → ℝ) ≃ᵐ (Fin a → ℝ) × (Fin b → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin a ⊕ Fin b => ℝ)
    (finSumFinEquiv (m := a) (n := b)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ))

theorem blockSplitEquiv_apply (J : Fin (a+b) → ℝ) :
    blockSplitEquiv a b J = (blockFast J, blockSlow J) := by
  ext <;> simp [blockSplitEquiv, blockFast, blockSlow, MeasurableEquiv.sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- The splitting of a block vector is volume preserving. -/
theorem measurePreserving_blockSplitEquiv (a b : ℕ) :
    MeasurePreserving (blockSplitEquiv a b) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin a ⊕ Fin b => ℝ)
      (finSumFinEquiv (m := a) (n := b)).symm)

theorem volume_joinedActions (X : Set (Fin a → ℝ)) (Y : Set (Fin b → ℝ)) :
    volume (joinedActions X Y) = volume X * volume Y := by
  have hp : joinedActions X Y = (blockSplitEquiv a b) ⁻¹' (X ×ˢ Y) := by
    ext J
    simp [blockSplitEquiv_apply, joinedActions]
  rw [hp, (measurePreserving_blockSplitEquiv a b).measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]

theorem domain_collar_helper {X : Set (Fin a → ℝ)} (hX : MeasurableSet X)
    {l u s E : ℝ} (hl : 0 < l) (hlu : l < u) (hs : 0 < s) (hsl : s < l)
    (hXfinite : volume X < ⊤) (hE : volume (realNbhd X s \ X) ≤ ENNReal.ofReal E) :
    volume (realNbhd (joinedActions X (actionShell b l u)) s \ joinedActions X (actionShell b l u)) ≤
      ENNReal.ofReal (E*(u-l+2*s)^b) + volume X *
        ENNReal.ofReal ((u-l+2*s)^b-(u-l)^b) := by
  set Y : Set (Fin b → ℝ) := actionShell b l u with hY
  set B : Set (Fin b → ℝ) := pi univ fun _ => Ioo (l - s) (u + s) with hB
  have hYm : MeasurableSet Y := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hYB : Y ⊆ B := fun y hy i _ => by
    have := hy i (mem_univ i)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hvY : volume Y = ENNReal.ofReal ((u - l) ^ b) := by
    rw [hY, actionShell, Real.volume_pi_Ioo]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, sub_eq_add_neg]
    rw [ENNReal.ofReal_pow (by linarith)]
  have hvB : volume B = ENNReal.ofReal ((u - l + 2 * s) ^ b) := by
    rw [hB, Real.volume_pi_Ioo]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow (by linarith)]
    congr 2; ring
  have hNB : realNbhd Y s ⊆ B := by
    rintro x ⟨y, hy, hd⟩ i _
    have h1 := hy i (mem_univ i)
    have h2 := (dist_pi_lt_iff hs).1 hd i
    rw [Real.dist_eq, abs_lt] at h2
    exact ⟨by linarith [h1.1, h2.1, h2.2], by linarith [h1.2, h2.1, h2.2]⟩
  have hsub : realNbhd (joinedActions X Y) s \ joinedActions X Y ⊆
      joinedActions (realNbhd X s \ X) B ∪ joinedActions X (B \ Y) := by
    intro x ⟨hx, hnx⟩
    rw [realNbhd_joinedActions] at hx
    by_cases h1 : blockFast x ∈ X
    · right
      exact ⟨h1, hNB hx.2, fun hy => hnx ⟨h1, hy⟩⟩
    · left
      exact ⟨⟨hx.1, h1⟩, hNB hx.2⟩
  have hd : 0 ≤ (u - l) ^ b := pow_nonneg (by linarith) _
  calc _ ≤ volume (joinedActions (realNbhd X s \ X) B ∪ joinedActions X (B \ Y)) :=
        measure_mono hsub
    _ ≤ volume (joinedActions (realNbhd X s \ X) B) + volume (joinedActions X (B \ Y)) :=
        measure_union_le _ _
    _ = volume (realNbhd X s \ X) * volume B + volume X * (volume B - volume Y) := by
        rw [volume_joinedActions, volume_joinedActions, measure_sdiff hYB hYm.nullMeasurableSet
          (by rw [hvY]; exact ENNReal.ofReal_ne_top)]
    _ ≤ ENNReal.ofReal E * ENNReal.ofReal ((u - l + 2 * s) ^ b) +
          volume X * (ENNReal.ofReal ((u - l + 2 * s) ^ b) - ENNReal.ofReal ((u - l) ^ b)) := by
        rw [hvB, hvY]
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_sub _ hd]
        congr 1
        rcases le_or_gt 0 E with hE0 | hE0
        · rw [ENNReal.ofReal_mul hE0]
        · rw [ENNReal.ofReal_of_nonpos hE0.le, zero_mul, ENNReal.ofReal_of_nonpos]
          exact mul_nonpos_of_nonpos_of_nonneg hE0.le (pow_nonneg (by linarith) _)

theorem collar {V : Set (Fin a → ℝ)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {A d : ℝ}
    (hc : ∀ s : ℝ, 0 < s → s < d →
      volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < s} ≤
        ENNReal.ofReal (A*s)) :
    (∀ t : ℝ, 0 < t →
      IsCompact (innerCore V t) ∧ innerCore V t ⊆ V ∧
      V \ innerCore V t =
        {I ∈ V | ∃ J ∈ frontier V, dist I J < t}) ∧
    (∀ t : ℝ, 0 < t → t < d →
      volume (V \ innerCore V t) ≤ ENNReal.ofReal (A*t) ∧
      volume V - ENNReal.ofReal (A*t) ≤ volume (innerCore V t)) ∧
    (∀ t s : ℝ, 0 < s → s < t →
      realNbhd (innerCore V t) s ⊆ V ∧
      realNbhd (innerCore V t) s \ innerCore V t ⊆ V \ innerCore V t) ∧
    (∀ t s : ℝ, 0 < s → s < t → t < d →
      volume (realNbhd (innerCore V t) s \ innerCore V t) ≤
        ENNReal.ofReal (A*t)) := by
  have hsub : ∀ t, innerCore V t ⊆ V := fun t I hI => hI.1
  have hdiff : ∀ t : ℝ, V \ innerCore V t = {I ∈ V | ∃ J ∈ frontier V, dist I J < t} := by
    intro t
    ext I
    simp [innerCore]
  have hcomp : ∀ t : ℝ, 0 < t → IsCompact (innerCore V t) := by
    intro t ht
    have hcl : innerCore V t = closure V ∩ ⋂ J ∈ frontier V, {I | t ≤ dist I J} := by
      ext I
      simp only [innerCore, mem_inter_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · rintro ⟨hI, h⟩
        exact ⟨subset_closure hI, h⟩
      · rintro ⟨hI, h⟩
        refine ⟨?_, h⟩
        by_contra hnV
        have := h I ⟨hI, fun h' => hnV (by rwa [hV.interior_eq] at h')⟩
        simp at this
        linarith
    have hclosed : IsClosed (innerCore V t) := by
      rw [hcl]
      exact isClosed_closure.inter (isClosed_biInter fun J _ => isClosed_le continuous_const
        (continuous_id.dist continuous_const))
    exact Metric.isCompact_of_isClosed_isBounded hclosed (hVb.subset (hsub t))
  have hnbhd : ∀ t s : ℝ, 0 < s → s < t → realNbhd (innerCore V t) s ⊆ V := by
    intro t s hs hst x ⟨y, hy, hd⟩
    by_contra hxV
    have hconn : IsPreconnected (segment ℝ y x) := (convex_segment y x).isPreconnected
    obtain ⟨J, hJ, hJf⟩ := ext_conn hconn ⟨y, left_mem_segment ℝ y x, hy.1⟩
      ⟨x, right_mem_segment ℝ y x, hxV⟩
    rw [segment_eq_image'] at hJ
    obtain ⟨θ, hθ, rfl⟩ := hJ
    have hle : dist y (y + θ • (x - y)) ≤ dist y x := by
      rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hθ.1, ← norm_neg (y - x), neg_sub]
      calc θ * ‖x - y‖ ≤ 1 * ‖x - y‖ := by gcongr; exact hθ.2
        _ = _ := one_mul _
    have := hy.2 _ hJf
    rw [dist_comm] at hd
    linarith
  have hvd : ∀ t : ℝ, volume (V \ innerCore V t) ≤
      volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < t} := by
    intro t
    refine measure_mono ?_
    rw [hdiff t]
    exact fun I hI => hI.2
  refine ⟨fun t ht => ⟨hcomp t ht, hsub t, hdiff t⟩, fun t ht htd => ?_,
    fun t s hs hst => ⟨hnbhd t s hs hst, fun x hx => ⟨hnbhd t s hs hst hx.1, hx.2⟩⟩,
    fun t s hs hst htd => ?_⟩
  · have h1 := (hvd t).trans (hc t ht htd)
    refine ⟨h1, ?_⟩
    rw [tsub_le_iff_right]
    calc volume V ≤ volume (innerCore V t ∪ (V \ innerCore V t)) :=
          measure_mono (fun x hx => by
            by_cases h : x ∈ innerCore V t
            · exact Or.inl h
            · exact Or.inr ⟨hx, h⟩)
      _ ≤ _ := (measure_union_le _ _).trans (by gcongr)
  · refine (measure_mono (μ := volume) (t := V \ innerCore V t)
      fun x hx => ⟨hnbhd t s hs hst hx.1, hx.2⟩).trans ?_
    exact (hvd t).trans (hc t (hs.trans hst) htd)

end KAM.Planetary

end
