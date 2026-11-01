/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Core
public import KAM.Planetary.Spatial.Geometry

/-!
# Safety of the spatial sharp core, for the whole ball

Package LP-SP-DOM, `LP:MAIN L18 (588–593)`, track LP, non-frozen. The statement surface is
proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

* `spatialChartSafe ν`: the collision-free part of the product chart domain.
* `spatialStrongAMD_le_spatialSlowDeficit`: `C ≤ C_{e₃} = (Σ slow²)/2` for *every* chart point
  (no alignment of `L` with `e₃`), from `spatialStrongAMD ≤ spatialFixedPlaneDeficit` (SP-PROD).
* D3 `spatialStrongCore_barrierState`: for `w` in the spatial core, `spatialPoincareProd ν w` is a
  `SpatialBarrierState ν U (3δ/16)` with `U = cthickening (4 r_g) L_δ`, even when `L` is not
  parallel to `e₃`.
* D3 `spatialStrongCore_subset_chartSafe`: hence the core lies in the collision-free chart domain.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- The collision-free part of the spatial product chart domain. -/
def spatialChartSafe (ν : Fin n → ℝ) : Set (Phase (n + (n + n))) :=
  spatialPoincareProdDom n ∩ spatialPoincareProd ν ⁻¹' spatialCollisionFreeDomain n

theorem spatialChartSafe_subset_dom (ν : Fin n → ℝ) :
    spatialChartSafe ν ⊆ spatialPoincareProdDom n :=
  inter_subset_left

/-- Chart images have negative energy, positive masses and no planet at the star. -/
theorem spatialNegativeEnergy_spatialPoincareProd (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    SpatialNegativeEnergy ν (spatialPoincareProd ν w) := by
  intro i
  have hE := spatialKeplerEnergy_spatialPoincareProd hν hw i
  have hI : 0 < (spatialBlock w i).2 0 := (hw i).1
  have hneg : spatialKeplerEnergy ν (spatialPoincareProd ν w) i < 0 := by
    rw [hE]
    have := hν i
    exact div_neg_of_neg_of_pos (by have := pow_pos this 3; linarith) (by positivity)
  refine ⟨hν i, ?_, hneg⟩
  by_contra h
  have h0 : spaceLength (bodyVector3 (spatialPoincareProd ν w).1 i) = 0 :=
    le_antisymm (not_lt.1 h) (spaceLength_nonneg _)
  have hlt := hneg
  unfold spatialKeplerEnergy at hlt
  rw [h0, div_zero, sub_zero] at hlt
  have := spaceSq_nonneg (bodyVector3 (spatialPoincareProd ν w).2 i)
  have h2 : 0 ≤ spaceSq (bodyVector3 (spatialPoincareProd ν w).2 i) / (2 * ν i) :=
    div_nonneg this (by have := hν i; positivity)
  linarith

/-- The action vector of a chart image is the fast action block. -/
theorem spatialActionVector_spatialPoincareProd (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialActionVector ν (spatialPoincareProd ν w) = fast w.2 := by
  funext i
  exact spatialKeplerAction_spatialPoincareProd hν hw i

/-- For every chart point (aligned or not), `C ≤ C_{e₃} = (Σ slow²)/2`. -/
theorem spatialStrongAMD_le_spatialSlowDeficit (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialStrongAMD ν (spatialPoincareProd ν w) ≤ spatialSlowDeficit w := by
  refine (spatialStrongAMD_le_spatialFixedPlaneDeficit ν _).trans ?_
  rw [spatialFixedPlaneDeficit_eq_half_slow_sq hν hw]
  rfl

/-- D3 (`LP:MAIN L18 (588–593)`): core points are spatial barrier states with margin `3δ/16`,
for the whole ball (47). -/
theorem spatialStrongCore_barrierState (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) {w : Phase (n + (n + n))}
    (hw : w ∈ spatialStrongCore ν L δ r) :
    SpatialBarrierState ν (sharedTube ν L δ r) (3 * δ / 16) (spatialPoincareProd ν w) := by
  have hdom : w ∈ spatialPoincareProdDom n := spatialStrongCore_subset_dom hν hn hg hδ hw
  obtain ⟨hI, hamd⟩ := spatialStrongCore_margin hν hn hg hw
  have hact := spatialActionVector_spatialPoincareProd hν hdom
  refine ⟨spatialNegativeEnergy_spatialPoincareProd hν hdom, by rw [hact]; exact hI, ?_⟩
  rw [hact]
  have := spatialStrongAMD_le_spatialSlowDeficit hν hdom
  linarith

/-- D3: the spatial core lies in the collision-free chart domain `spatialChartSafe ν`. -/
theorem spatialStrongCore_subset_chartSafe (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    spatialStrongCore ν L δ r ⊆ spatialChartSafe ν := by
  obtain ⟨K, -, hKsub, hbar⟩ := exists_spatialBarrierCompact hν hn hg.compact hg.subset_chamber
    (m := 3 * δ / 16) (by positivity)
  intro w hw
  exact ⟨spatialStrongCore_subset_dom hν hn hg hδ hw,
    hKsub (hbar _ (spatialStrongCore_barrierState hν hn hg hδ hw))⟩

end KAM.Planetary.Spatial

end
