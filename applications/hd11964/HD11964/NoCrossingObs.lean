/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import HD11964.ReducedRange
public import KAM.Application.LambdaDrift.ObservableNoCrossing

/-!
# HD 11964: no orbit crossing, the first exit driven by the reduced Delaunay actions

Scoping note `docs/tracks/LP/REDUCED-MASS-SCOPE.md` §4, for HD 11964. The observable counterpart of
`HD11964.noCrossing_of_regionBounds`.

The observable is the reduced Delaunay action in the chart, `G_i = reducedAction i`
(`HD11964.ReducedRange`). The approximate integrals `F_i` are built against it, so the range of
`F_i - G_i` on the region no longer contains the oscillation of the heliocentric `Λ_b`
(≈ `2 μ ν Λ e`); that oscillation, the range of `G_i - Λ_i` on `R(r)`, is charged against
`r / 2 - d`.

* `chartTube_subset_region`: the chart tube of every initial state of the neighbourhood lies in
  `R(r)` (`HD11964.region`), so a bound of `G - Λ` on the fixed set `R(r)` serves every initial
  state.
* `noCrossing_of_regionBounds_obs`: **conditional on the certificate's bounds** — the bracket bound
  `|dF_i (X_H)| ≤ η_i` and the range `lo_i ≤ F_i - G_i ≤ hi_i` on `R(d + ε)`, the range
  `loG_i ≤ G_i - Λ_i ≤ hiG_i` on `R(r)`, and decided drift data `D` (`D.ok = true`,
  `D.r = 1/250`).
* `noCrossing_of_regionBounds_obs_analytic`: the same with the range of `G - Λ` discharged by the
  analytic bound `reducedAction_sub_mem_region` (`D.loG ≤ loGan`, `hiGan ≤ D.hiG`, decided); only
  the bounds `hη`, `hFG` on `R(d + ε)` remain.

The separations `dStar`, `dPair` are LP0's existential constants, the same as in
`noCrossing_of_regionBounds`.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift

namespace HD11964

/-- The chart tube of an initial state of the neighbourhood lies in `R(r)`. -/
theorem chartTube_subset_region {z₀ : Phase (2 * 2)}
    (hbox : ∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i)
    (hC : strongAMD nu z₀ ≤ cBar) : chartTube nu z₀ rTube ⊆ region rTube := by
  rintro w ⟨hw, hΛ, hA⟩
  refine mem_region hbox hC hw (fun i => ?_) hA
  have h := norm_le_pi_norm (fast w.2 - actionVector nu z₀) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at h
  exact h.trans hΛ.le

/-- **HD 11964: no orbit crossing, the first exit driven by the reduced actions** (conditional on
the per-region bounds of the certificate; not the headline).

There are LP0's constants `dStar, dPair > 0` such that, for decided drift data `D` with
`D.r = 1/250`, the range `loG_i ≤ G_i - Λ_i ≤ hiG_i` of the reduced actions `G` on `R(r)`, and
functions `F` differentiable on an open `O ⊇ R(d + ε)` with `|dF_i (X_H)| ≤ η_i` and
`lo_i ≤ F_i - G_i ≤ hi_i` on `R(d + ε)` (for the HD 11964 masses `ν`, `μ`), every physical initial
state with actions in `[Λlo, Λhi]`, strong AMD at most `1/100` and positive angular momentum has a
unique moving solution on `[-T, T]` along which the orbits keep LP0's separations. -/
theorem noCrossing_of_regionBounds_obs :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : ObsDriftData 2), D.ok = true → (D.r : ℝ) = rTube →
      (∀ i, ∀ w ∈ region rTube, (D.loG i : ℝ) ≤ reducedAction i w - fast w.2 i ∧
        reducedAction i w - fast w.2 i ≤ D.hiG i) →
      ∀ (F : Fin 2 → Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))),
        IsOpen O → region ((D.d : ℝ) + D.eps) ⊆ O → (∀ i, DifferentiableOn ℝ (F i) O) →
        (∀ i, ∀ w ∈ region ((D.d : ℝ) + D.eps),
          |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam nu mu) w)| ≤ D.eta i) →
        (∀ i, ∀ w ∈ region ((D.d : ℝ) + D.eps),
          (D.lo i : ℝ) ≤ F i w - reducedAction i w ∧ F i w - reducedAction i w ≤ D.hi i) →
      ∀ z₀ : Phase (2 * 2), IsPhysicalState nu z₀ →
        (∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i) →
        strongAMD nu z₀ ≤ cBar → 0 < totalMomentum z₀ →
        ∃ z : ℝ → Phase (2 * 2), z 0 = z₀ ∧
          IsMovingSolutionOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
          MovingUniqueOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
          ∀ t ∈ Icc (-(D.T : ℝ)) D.T,
            (∀ i, dStar ≤
              keplerAxis nu (z t) i * (1 - planeLength (keplerEccVector nu (z t) i))) ∧
            (∀ a : AdjIdx 2, dPair ≤ keplerAxis nu (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector nu (z t) a.upperIdx)) -
              keplerAxis nu (z t) a.1 * (1 + planeLength (keplerEccVector nu (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) := by
  obtain ⟨dS, dP, hdS, hdP, hmain⟩ := noCrossing_of_approxIntegrals_obs le_rfl nu nu_pos
    actionBox isCompact_actionBox actionBox_subset_chamber delta delta_pos
  refine ⟨dS, dP, hdS, hdP, fun D hD hr hGΛ F O hO hRO hF hη hFG z₀ hphys hbox hC hL => ?_⟩
  have hd := liftData hphys hbox hC hL
  rw [← hr] at hd
  have htube : chartTube nu z₀ D.r ⊆ region rTube := by
    rw [hr]; exact chartTube_subset_region hbox hC
  exact hmain D hD mu z₀ hd reducedAction F (region ((D.d : ℝ) + D.eps)) O
    (fun i => (continuousOn_reducedAction i).mono htube) (fun i w hw => hGΛ i w (htube hw))
    hO hRO hF (fun _ _ _ w hw _ hΛ hA => mem_region hbox hC hw hΛ hA) hη hFG

/-- **HD 11964: no orbit crossing, the first exit driven by the reduced actions, with the range of
`G - Λ` analytic** (conditional on the certificate's bounds `hη`, `hFG` on `R(d + ε)`; not the
headline). As `noCrossing_of_regionBounds_obs`, with the range of `G - Λ` on `R(r)` discharged by
`reducedAction_sub_mem_region`: the drift data need only `D.loG_i ≤ loGan_i` and
`hiGan_i ≤ D.hiG_i`. -/
theorem noCrossing_of_regionBounds_obs_analytic :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : ObsDriftData 2), D.ok = true → (D.r : ℝ) = rTube →
      (∀ i, D.loG i ≤ loGan i ∧ hiGan i ≤ D.hiG i) →
      ∀ (F : Fin 2 → Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))),
        IsOpen O → region ((D.d : ℝ) + D.eps) ⊆ O → (∀ i, DifferentiableOn ℝ (F i) O) →
        (∀ i, ∀ w ∈ region ((D.d : ℝ) + D.eps),
          |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam nu mu) w)| ≤ D.eta i) →
        (∀ i, ∀ w ∈ region ((D.d : ℝ) + D.eps),
          (D.lo i : ℝ) ≤ F i w - reducedAction i w ∧ F i w - reducedAction i w ≤ D.hi i) →
      ∀ z₀ : Phase (2 * 2), IsPhysicalState nu z₀ →
        (∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i) →
        strongAMD nu z₀ ≤ cBar → 0 < totalMomentum z₀ →
        ∃ z : ℝ → Phase (2 * 2), z 0 = z₀ ∧
          IsMovingSolutionOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
          MovingUniqueOn nu mu (Icc (-(D.T : ℝ)) D.T) z ∧
          ∀ t ∈ Icc (-(D.T : ℝ)) D.T,
            (∀ i, dStar ≤
              keplerAxis nu (z t) i * (1 - planeLength (keplerEccVector nu (z t) i))) ∧
            (∀ a : AdjIdx 2, dPair ≤ keplerAxis nu (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector nu (z t) a.upperIdx)) -
              keplerAxis nu (z t) a.1 * (1 + planeLength (keplerEccVector nu (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) := by
  obtain ⟨dS, dP, hdS, hdP, hmain⟩ := noCrossing_of_regionBounds_obs
  refine ⟨dS, dP, hdS, hdP, fun D hD hr hG => hmain D hD hr fun i w hw => ?_⟩
  obtain ⟨h1, h2⟩ := reducedAction_sub_mem_region (i := i) hw
  have h3 : (D.loG i : ℝ) ≤ loGan i := by exact_mod_cast (hG i).1
  have h4 : (hiGan i : ℝ) ≤ D.hiG i := by exact_mod_cast (hG i).2
  exact ⟨h3.trans h1, h2.trans h4⟩

end HD11964

end
