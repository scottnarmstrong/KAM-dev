/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.Nek.PlanarSafety.Source

/-!
# Provider of the anchor `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`

Anchor (track LP, `LP:MAIN T15 (502–506) with §1 (6)–(9)
(69–93) without (5), L14 (468–500), L16 (508–529); N8, N10; drift supplier L12–L13 (381–467)
replaced by the sealed partialConvex_nekhoroshev (LP3-PLAN
§1–§2)`). The anchor text is in docs/tracks/LP/freeze/draft8/.

The proof of `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith` is assembled here
as `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`: the anchor's exact
type text, proved in one line by the implementation theorem
`KAM.Planetary.StrongAMD.lp3_planar_strongAMD_safety_source`. This module is quarantined (AGENTS
rule 9): no module other than the anchor may import it.
-/

@[expose] public section

namespace KAM.Provider.Planetary.StrongAMD

open KAM.Planetary KAM.Planetary.StrongAMD

/-- Quarantined provider of the frozen theorem
`KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`. -/
theorem planar_strongAMD_exponentialSafety_noArith {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0,
        sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
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
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              |sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) -
                  sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν)| ≤
                n * AΛ * μ ^ planetaryDriftExponent n) ∧
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
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1)) :=
  lp3_planar_strongAMD_safety_source hn ν hν hνmax hνle A hA hAord δ hδ

end KAM.Provider.Planetary.StrongAMD

end
