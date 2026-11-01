/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import HD11964.Threshold
public import KAM.Application.LambdaDrift.NoCrossing
public import KAM.Application.LambdaDrift.Rotation

/-!
# HD 11964: no orbit crossing, given the certificate's bounds on the region `R(d)`

Design `docs/campaign/design/HD11964-PILOT.md` §2–§4. The certificate region of design §3 is
`R(d) = {w ∈ chartSafe ν : Λ ∈ [Λlo - d, Λhi + d], ΣΓ ≤ Cbar + 2d}` (`region`). It is fixed: it does
not depend on the initial state, and it contains every chart state reachable with action drift
`≤ d` from any initial state of the neighbourhood (`mem_region`, by exact conservation of `L`).
It is invariant under the chart rotation (`chartRot_mem_region`), so a cover need only cover it
modulo rotation (`KAM.Application.LambdaDrift.bracket_bound_of_rotation`).

`noCrossing_of_regionBounds` is **conditional on the certificate's per-region bounds** (the outputs
of the cell checks and the cover of phase 2, part B): the bracket bound `|dF_i (X_H)| ≤ η_i` and the
range `lo_i ≤ F_i - Λ_i ≤ hi_i` on `R(d)`, with decided drift data `D` (`D.ok = true`, `D.r = 1/250`).
It is not the headline: the headline discharges these hypotheses by the kernel-checked certificate.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift

namespace HD11964

/-- The certificate region `R(d)` (design §3): chart states of `chartSafe ν` with actions in
`[Λlo - d, Λhi + d]` and chart AMD at most `Cbar + 2d`. -/
def region (d : ℝ) : Set (Phase (2 + 2)) :=
  {w | w ∈ chartSafe nu ∧ (∀ i, lamLo i - d ≤ fast w.2 i ∧ fast w.2 i ≤ lamHi i + d) ∧
    chartAMD w ≤ cBar + 2 * d}

/-- `R(d)` contains every chart state of `chartSafe ν` within action distance `d` of an initial
state of the neighbourhood whose chart AMD is at most `C(z₀) + 2d` (the inclusion `hR` of the
bridge, for every initial state at once). -/
theorem mem_region {d : ℝ} {z₀ : Phase (2 * 2)}
    (hbox : ∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i)
    (hC : strongAMD nu z₀ ≤ cBar) {w : Phase (2 + 2)} (hw : w ∈ chartSafe nu)
    (hΛ : ∀ i, |fast w.2 i - actionVector nu z₀ i| ≤ d)
    (hA : chartAMD w ≤ strongAMD nu z₀ + ((2 : ℕ) : ℝ) * d) : w ∈ region d := by
  refine ⟨hw, fun i => ?_, ?_⟩
  · have h1 := abs_le.1 (hΛ i)
    have h2 := hbox i
    have h3 : actionVector nu z₀ i = keplerAction nu z₀ i := rfl
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · push_cast at hA
    linarith

/-- `R(d)` is invariant under the chart rotation (design §9). -/
theorem chartRot_mem_region (θ : ℝ) {d : ℝ} {w : Phase (2 + 2)} (hw : w ∈ region d) :
    chartRot θ w ∈ region d := by
  obtain ⟨hs, hΛ, hA⟩ := hw
  refine ⟨chartRot_mem_chartSafe nu θ hs, ?_, ?_⟩
  · rw [fast_chartRot]; exact hΛ
  · rw [chartAMD_chartRot]; exact hA

/-- **HD 11964: no orbit crossing, given the certificate's bounds on `R(d)`** (conditional on the
per-region bounds of the certificate; not the headline).

There are LP0's constants `dStar, dPair > 0` such that, for decided drift data `D` with
`D.r = 1/250`, functions `F` differentiable on an open `O ⊇ R(D.d)` with `|dF_i (X_H)| ≤ η_i` and
`lo_i ≤ F_i - Λ_i ≤ hi_i` on `R(D.d)` (for the HD 11964 masses `ν`, `μ`), every physical initial
state with actions in `[Λlo, Λhi]`, strong AMD at most `1/100` and positive angular momentum has a
unique moving solution on `[-T, T]` along which the orbits keep LP0's separations. -/
theorem noCrossing_of_regionBounds :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : DriftData 2), D.ok = true → (D.r : ℝ) = rTube →
      ∀ (F : Fin 2 → Phase (2 + 2) → ℝ) (O : Set (Phase (2 + 2))),
        IsOpen O → region D.d ⊆ O → (∀ i, DifferentiableOn ℝ (F i) O) →
        (∀ i, ∀ w ∈ region D.d,
          |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam nu mu) w)| ≤ D.eta i) →
        (∀ i, ∀ w ∈ region D.d,
          (D.lo i : ℝ) ≤ F i w - fast w.2 i ∧ F i w - fast w.2 i ≤ D.hi i) →
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
  obtain ⟨dS, dP, hdS, hdP, hmain⟩ := noCrossing_of_approxIntegrals le_rfl nu nu_pos actionBox
    isCompact_actionBox actionBox_subset_chamber delta delta_pos
  refine ⟨dS, dP, hdS, hdP, fun D hD hr F O hO hRO hF hη hG z₀ hphys hbox hC hL => ?_⟩
  have hd := liftData hphys hbox hC hL
  rw [← hr] at hd
  exact hmain D hD mu z₀ hd F (region D.d) O hO hRO hF
    (fun w hw hΛ hA => mem_region hbox hC hw hΛ hA) hη hG

end HD11964

end
