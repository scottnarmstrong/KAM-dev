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
range `lo_i ≤ F_i - Λ_i ≤ hi_i` on `R(d)`, with decided drift data `D` (`D.ok = true`, decided by
`decide +kernel`; `D.r = 1/250`). It is not the headline: the headline discharges these hypotheses
by the kernel-checked certificate. The separations `dStar`, `dPair` are LP0's existential
constants: positive, not explicit.

`initial_of_chart` shows the initial set is not empty: every chart state with actions in
`[Λlo, Λhi]` and chart AMD at most `1/100` (every phase, every perihelion, eccentricities up to the
AMD bound) satisfies the hypotheses on `z₀`; `initialSet_nonempty` is the circular coplanar
instance. That the nominal elements of design §1 are such a state (`ΣΓ = 0.009455 ≤ 1/100`, `Λ̂` in
the box) is a numerical check (`validation/threshold.json`), not a Lean lemma.
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

/-- **The initial set covers every chart state of the box.** For a chart point with actions in
`[Λlo, Λhi]` and chart AMD `ΣΓ ≤ 1/100`, its image `z₀ = Ψ w` is physical, has Kepler actions in
`[Λlo, Λhi]`, strong AMD at most `1/100` and positive angular momentum. -/
theorem initial_of_chart {w : Phase (2 + 2)} (hΛ : ∀ i, lamLo i ≤ fast w.2 i ∧ fast w.2 i ≤ lamHi i)
    (hA : chartAMD w ≤ cBar) :
    IsPhysicalState nu (poincareProd nu 1 w) ∧
      (∀ i, lamLo i ≤ keplerAction nu (poincareProd nu 1 w) i ∧
        keplerAction nu (poincareProd nu 1 w) i ≤ lamHi i) ∧
      strongAMD nu (poincareProd nu 1 w) ≤ cBar ∧ 0 < totalMomentum (poincareProd nu 1 w) := by
  have hlo : ∀ i, cBar < lamLo i := by
    intro i; fin_cases i <;> norm_num [lamLo, cBar]
  have hpos : ∀ i, 0 < fast w.2 i := fun i =>
    lt_of_lt_of_le (lt_trans (by norm_num [cBar]) (hlo i)) (hΛ i).1
  have hdom : w ∈ poincareProdDom 2 := by
    intro i
    have hΓ : poincareGamma (planetBlock w i) = lpGamma w i := by
      simp [poincareGamma, lpGamma, planetBlock, slow]
    have h0 : (planetBlock w i).2 0 = fast w.2 i := by simp [planetBlock]
    have hle : lpGamma w i ≤ chartAMD w := by
      rw [chartAMD_eq_sum_lpGamma]
      exact Finset.single_le_sum (f := lpGamma w) (fun j _ => by unfold lpGamma; positivity)
        (Finset.mem_univ i)
    have hc : cBar < fast w.2 i := lt_of_lt_of_le (hlo i) (hΛ i).1
    refine ⟨by rw [h0]; exact hpos i, ?_⟩
    rw [hΓ, h0]
    linarith
  have hpro := (sec_domain_chart_facts nu_pos hdom).1
  refine ⟨fun i => ⟨(hpro i).2.1, (hpro i).2.2.1⟩, fun i => ?_, ?_, ?_⟩
  · rw [lpChart_action nu_pos hdom i]
    exact hΛ i
  · rw [lpChart_strongAMD nu_pos hdom]
    exact hA
  · unfold totalMomentum
    exact Finset.sum_pos (fun i _ => (hpro i).2.2.2) Finset.univ_nonempty

/-- **The initial set is not empty**: the circular coplanar state with actions `Λlo` and zero
phases satisfies every hypothesis on `z₀` of `noCrossing_of_regionBounds`. -/
theorem initialSet_nonempty :
    ∃ z₀ : Phase (2 * 2), IsPhysicalState nu z₀ ∧
      (∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i) ∧
      strongAMD nu z₀ ≤ cBar ∧ 0 < totalMomentum z₀ := by
  let w₀ : Phase (2 + 2) :=
    assemble lamLo (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ)
  have h1 : fast w₀.2 = lamLo := funext fun j => Fin.append_left _ _ j
  have h2 : chartAMD w₀ = 0 := by simp [w₀, chartAMD, assemble, slow]
  refine ⟨poincareProd nu 1 w₀, initial_of_chart (fun i => ?_) ?_⟩
  · rw [h1]
    refine ⟨le_rfl, ?_⟩
    fin_cases i <;> norm_num [lamLo, lamHi]
  · rw [h2]
    norm_num [cBar]

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
