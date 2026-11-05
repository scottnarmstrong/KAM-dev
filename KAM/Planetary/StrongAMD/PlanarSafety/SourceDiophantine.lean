/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.PlanarSafety.Source
public import KAM.Planetary.StrongAMD.PlanarSafety.SourceCorollary
public import KAM.Planetary.StrongAMD.DiophantineBridge

/-!
# LP1 and LP1-H with the frozen Diophantine predicate

Source: `LP:MAIN T15 (502–506)`, `§1 (5) (60–65)`,
`§1 (93)`; track LP, non-frozen.

`lp1_planar_strongAMD_safety_source_isDiophantine` and its `τ = n - 1/2` form are the statements
of `lp1_planar_strongAMD_safety_source` and
`lp1_planar_strongAMD_safety_source_halfInteger` with the
Diophantine premise written as the frozen `KAM.IsDiophantine γ τ (fun i => ν i ^ 3 / Λ_i ^ 3)`
(D20) instead of `∀ k ≠ 0, γ * modeSize k ^ (-τ) ≤ |k · ω|`; the two premises are literally
equivalent (`isDiophantine_iff_forall_modeSize`), so nothing is added or weakened. They are the
closing theorems of the frozen anchors LP1, LP1-H.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary

/-- **LP1 with the frozen Diophantine predicate** (`LP:MAIN T15 (502–506)`, `§1 (5)`): the statement
of `lp1_planar_strongAMD_safety_source` with its Diophantine premise as `KAM.IsDiophantine`. -/
theorem lp1_planar_strongAMD_safety_source_isDiophantine {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        KAM.IsDiophantine γ τ (fun i => ν i ^ 3 / keplerAction ν z₀ i ^ 3) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0,
        sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => keplerAction ν (z t) i) ∈ chamber ν,
              ∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              |sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) -
                  sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν)| ≤
                n * AΛ * Real.sqrt μ) ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i *
              (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
             ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧
                  oscEnergy ν μ (z t) i < 0 ∧ oscEcc ν μ (z t) i < 1,
              (∀ i, sourceOscEnergy (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  sourceOscEcc (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 1 ∧
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ≤
                    planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  |sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerAxis ν (z t) i| +
                    planeLength (sourceOscEccVector (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
              (∀ i, |sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerPeri (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ ∧
                  |sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerApo (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.upperIdx -
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1)) := by
  simp only [isDiophantine_iff_forall_modeSize]
  exact lp1_planar_strongAMD_safety_source hn ν hν hνmax hνle A hA hAord δ γ τ hδ hγ hτ

/-- **LP1 at `τ = n - 1/2` with the frozen Diophantine predicate** (`LP:MAIN §1 (93)`,
`T15 (502–506)`): `lp1_planar_strongAMD_safety_source_halfInteger` with its Diophantine premise as
`KAM.IsDiophantine γ ((n : ℝ) - 1 / 2)`. -/
theorem lp1_planar_strongAMD_safety_source_isDiophantine_halfInteger {n : ℕ} (hn : 2 ≤ n)
    (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        KAM.IsDiophantine γ ((n : ℝ) - 1 / 2) (fun i => ν i ^ 3 / keplerAction ν z₀ i ^ 3) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0,
        sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (n : ℝ) + 1))))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => keplerAction ν (z t) i) ∈ chamber ν,
              ∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              |sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) -
                  sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν)| ≤
                n * AΛ * Real.sqrt μ) ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i *
              (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
             ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧
                  oscEnergy ν μ (z t) i < 0 ∧ oscEcc ν μ (z t) i < 1,
              (∀ i, sourceOscEnergy (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  sourceOscEcc (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 1 ∧
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ≤
                    planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  |sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerAxis ν (z t) i| +
                    planeLength (sourceOscEccVector (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
              (∀ i, |sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerPeri (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ ∧
                  |sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerApo (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.upperIdx -
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1)) := by
  simp only [isDiophantine_iff_forall_modeSize]
  exact lp1_planar_strongAMD_safety_source_halfInteger hn ν hν hνmax hνle A hA hAord δ γ hδ hγ

end KAM.Planetary.StrongAMD

end
