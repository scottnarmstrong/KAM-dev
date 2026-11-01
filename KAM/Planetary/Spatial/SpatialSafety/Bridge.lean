/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.ChartLift
public import KAM.Planetary.Spatial.NonresonantReuse

/-!
# Joining the chart-lift premises to the spatial stopped drift

Package LP-SP-SAFE (spatial theorem LP2; `LP:MAIN L14 (468–500)`, `L13 (429–464)`, `L18`), track
LP, non-frozen.

LP-SP-LIFT (`spatialChartLift_premises`) and LP-SP-NRR (`spatial_stopped_drift`) were proved
independently and carry their own names for the same chart objects.  This module records the
identifications, all by unfolding and `ext`:

* `spLiftSecularBall = spatialSecularBall` (the ball (47) in `Phase (n + n)`), hence
  `spatialStoppedBlock = lpBlockNM` (the Lemma 13 block);
* `spLiftChartSafe = spatialChartSafe` (definitionally);
* `spLiftChartHam` and `lpChartHamNM` have the same Hamilton field on the open chart domain.

`SpatialLiftData.spatialChartLift_premises_nrr` restates the LIFT premises in exactly the shape
consumed by `spatial_stopped_drift`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Nekhoroshev KAM.Weighted KAM.NormalForm Set

variable {n : ℕ}

/-- The two ball (47) definitions agree. -/
theorem spLiftSecularBall_eq_spatialSecularBall (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) :
    spLiftSecularBall ν δ I0 = spatialSecularBall ν δ I0 := by
  ext y
  simp only [spLiftSecularBall, spatialSecularBall, mem_ofPred_eq]
  rw [← Finset.sum_add_distrib]
  constructor <;> intro h <;> convert h using 2 <;>
    simp only [Finset.sum_div, add_div]

/-- The Lemma 13 block of LP-SP-LIFT and of LP-SP-NRR coincide. -/
theorem spatialStoppedBlock_eq_lpBlockNM (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) (r w : ℝ) :
    spatialStoppedBlock ν δ I0 r w = lpBlockNM ν δ I0 r w := by
  simp only [spatialStoppedBlock, lpBlockNM, spLiftSecularBall_eq_spatialSecularBall]

/-- The chart-safe sets coincide. -/
theorem spLiftChartSafe_eq_spatialChartSafe (ν : Fin n → ℝ) :
    spLiftChartSafe ν = spatialChartSafe ν := rfl

/-- The NRR chart Hamiltonian is the pulled-back Hamiltonian. -/
theorem lpChartHamNM_eq_spatialPulledHam (ν : Fin n → ℝ) (μ : ℝ) :
    lpChartHamNM ν μ = spatialPulledHam ν μ := rfl

namespace SpatialLiftData

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 3)} {δ r : ℝ}

/-- **The D1 premises of `spatial_stopped_drift`** (`LP:MAIN L14 (477–483)`, `L13`, `L18`): from
the lift data and a stopped spatial moving solution, a chart curve `w` on `uIcc 0 t` satisfying
exactly the lift, localization, initial-action and slow-ball hypotheses of LP-SP-NRR's
`spatial_stopped_drift` for the block `lpBlockNM ν δ (Λ z₀) r wS`. -/
theorem spatialChartLift_premises_nrr (hd : SpatialLiftData ν U z₀ δ r) {wS : ℝ} {μ : ℝ}
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 3)}
    (hz : IsSpatialMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (hs : SpatialStoppedOn ν z₀ δ r z t) :
    ∃ w : ℝ → Phase (n + (n + n)),
      (∀ u ∈ uIcc 0 t, w u ∈ spatialChartSafe ν ∧ spatialPoincareProd ν (w u) = z u ∧
        HasDerivAt w (hamiltonianVectorField (lpChartHamNM ν μ) (w u)) u) ∧
      (∀ u ∈ uIcc 0 t,
        lpRescaleNM (lpBlockNM ν δ (spatialActionVector ν z₀) r wS).lam (w u) ∈
          (lpBlockNM ν δ (spatialActionVector ν z₀) r wS).realDom
            (lpBlockNM ν δ (spatialActionVector ν z₀) r wS).rB) ∧
      fast (w 0).2 = spatialActionVector ν z₀ ∧
      (∀ u ∈ uIcc 0 t, (slow (w u).1, slow (w u).2) ∈ spatialSecularBall ν δ
        (spatialActionVector ν z₀)) := by
  obtain ⟨w, hlift, hmem, hinit, hS⟩ :=
    hd.spatialChartLift_premises (wS := wS) hJ h0 hz hz0 ht hs
  rw [spatialStoppedBlock_eq_lpBlockNM] at hmem hinit hS
  refine ⟨w, fun u hu => ⟨(hlift u hu).1, (hlift u hu).2.1, ?_⟩, hmem, ?_, hS⟩
  · have := (hlift u hu).2.2
    rwa [spLiftChartHam_field_eq hd.pos_mass μ (hlift u hu).1] at this
  · simpa [fastAction_lpRescaleNM, lpBlockNM] using hinit

end SpatialLiftData

end KAM.Planetary.Spatial

end
