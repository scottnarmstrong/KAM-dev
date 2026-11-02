/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.SourceCarrier
public import KAM.Planetary.Spatial.Nek.SpatialSafety.Main

/-!
# The Nekhoroshev part restated through the spatial source carriers (OD-11 option (b), D59)

Source: (`LP:MAIN T19 (599–603)` with `L14 (468–500)`, `L16 (508–529)`, `d = 3`), track LP,
non-frozen.

* `lp3_spatial_strongAMD_safety_source`: the text of `lp2_spatial_strongAMD_safety_source`
  (every canonical element through `spatialSource*`)
  with exactly three changes: the data `γ τ`, the premises `hγ hτ` and the Diophantine premise are
  removed; the time is `T₀ * exp (c * μ ^ (-planetaryTimeExponent n))`; the drift lines (action,
  axis, AMD) read `μ ^ planetaryDriftExponent n` instead of `√μ`.
* `lp3_spatial_strongAMD_safety_source_general`: the same without `hνmax`, `hνle`.

Both are proved from `lp3_spatial_strongAMD_safety` (resp. `…_normalized`); the guards come from
its conclusions.  The planar twin is `lp3_planar_strongAMD_safety_source`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **The Nekhoroshev part through the spatial source carriers, without the normalization premises**
(`LP:MAIN T19 (599–603)` with `L14 (468–500)`, `L16 (508–529)`).
Every canonical element at `z₀` and `z t` is a `spatialSource*` restriction. -/
theorem lp3_spatial_strongAMD_safety_source_general (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * μ ^ planetaryDriftExponent n ∧
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
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1) :=
  by
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    lp3_spatial_strongAMD_safety hn ν hν A hA hAord δ hδ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys h₀ hAz hch hC0 T
  obtain ⟨z, hz0, hsol, huniq, hnewt, hall⟩ :=
    H μ hμ hμle z₀ hphys hAz hch hC0
  refine ⟨z, hz0, hsol, huniq, hnewt, fun t ht => ?_⟩
  obtain ⟨hph, ⟨hcht, hamd⟩, hΛ, ha, hdrift, hs1, hs2, hd1, hd2, hosc, hpa, hd3, hd4⟩ :=
    hall t ht
  have hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
      spatialKeplerEnergy ν (z t) i < 0 := fun i => ⟨hν i, hph i⟩
  have ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
      ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
        spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1 :=
    ⟨hν, hμ, fun i => ⟨(hph i).1, (hosc i).1, (hosc i).2.2.1⟩⟩
  exact ⟨hs, hcht, hamd, hΛ, ha, hdrift, hs1, hs2, hd1, hd2, ho, hosc, hpa, hd3, hd4⟩

/-- **The Nekhoroshev part through the spatial source carriers, with MAIN's mass normalization** (`hνmax`,
`hνle`; unused premises). Every canonical element is a `spatialSource*` restriction. -/
theorem lp3_spatial_strongAMD_safety_source (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * μ ^ planetaryDriftExponent n ∧
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
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1) :=
  by
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    lp3_spatial_strongAMD_safety_normalized hn ν hν hνmax hνle A hA hAord δ hδ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys h₀ hAz hch hC0 T
  obtain ⟨z, hz0, hsol, huniq, hnewt, hall⟩ :=
    H μ hμ hμle z₀ hphys hAz hch hC0
  refine ⟨z, hz0, hsol, huniq, hnewt, fun t ht => ?_⟩
  obtain ⟨hph, ⟨hcht, hamd⟩, hΛ, ha, hdrift, hs1, hs2, hd1, hd2, hosc, hpa, hd3, hd4⟩ :=
    hall t ht
  have hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
      spatialKeplerEnergy ν (z t) i < 0 := fun i => ⟨hν i, hph i⟩
  have ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
      ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
        spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1 :=
    ⟨hν, hμ, fun i => ⟨(hph i).1, (hosc i).1, (hosc i).2.2.1⟩⟩
  exact ⟨hs, hcht, hamd, hΛ, ha, hdrift, hs1, hs2, hd1, hd2, ho, hosc, hpa, hd3, hd4⟩

end KAM.Planetary.Spatial

end
