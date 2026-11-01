/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.SpatialSafety.SourceCorollary

/-!
# Provider for `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger`

Provider for the frozen theorem
`KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger`, draft-7 revision-1 anchor
LP2-H (spatial strong-AMD exponential safety at τ = n − 1/2 (exponent 1/(2n+1))); track LP, package
LP-FREEZE7R (`LP:MAIN §1 (93) (τ = n − 1/2), T19 (599–603), L16 (508–529), d = 3`). The statement
surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The theorem `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger` states
the anchor's exact type text (its draft file under `docs/tracks/LP/freeze/draft7/`) and is proved in
one line by the implementation theorem
`KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_isDiophantine_halfInteger`. While the
frozen anchor is `DRAFT_SORRY` (or not yet created), this module is quarantined: no module other
than the anchor may import it (AGENTS rule 9).
-/

@[expose] public section

namespace KAM.Provider.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD KAM.Planetary.Spatial

theorem spatial_strongAMD_exponentialSafety_halfInteger {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        KAM.IsDiophantine γ ((n : ℝ) - 1 / 2) (fun i => ν i ^ 3 /
            spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i ^ 3) →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (n : ℝ) + 1))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialSourceBarycentricPositions ν μ hν hμ (z t).1)
            (fun t => spatialSourceBarycentricVelocities ν μ hν hμ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * Real.sqrt μ ∧
            (∀ i, dStar ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∧
            (∀ a : AdjIdx n, dPair ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.upperIdx -
                  spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.1) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                  spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1,
              (∀ i, spatialSourceOscEnergy (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  spatialSourceOscEcc (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 1 ∧
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ≤
                    spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  |spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerEccVector
                        (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ≤ Aelem * μ) ∧
              (∀ i, |spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ ∧
                  |spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ)
                      a.upperIdx -
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1) := by
  exact _root_.KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_isDiophantine_halfInteger
    hn ν hν hνmax hνle A hA hAord δ γ hδ hγ

end KAM.Provider.Planetary.Spatial

end
