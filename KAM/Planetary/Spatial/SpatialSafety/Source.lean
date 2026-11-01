/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.SourceCarrier
public import KAM.Planetary.Spatial.SpatialSafety.Main

/-!
# LP2 restated through the spatial source carriers (OD-11 option (b))

Package LP-SP-SRCB (`LP:MAIN T19 (599–603)`, `L16 (508–529)`, `d = 3`), track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

* `lp2_spatial_strongAMD_safety_source`: the LP2 text (§3c, with `hνmax`, `hνle`) in which every
  conclusion occurrence of `spatialStrongAMD`, `spatialKeplerPeri/Apo` and
  `spatialOscEnergy/Axis/Ecc/EccVector/Peri/Apo` is replaced by its source version
  (`spatialSource*`).  The subtype proofs are existential in the conclusion (`∃ hs, …`,
  `∃ ho, …`), mirroring `∃ hcht` for the thresholds; the initial AMD hypothesis is
  `spatialSourceStrongAMD ⟨z₀, h₀⟩ ≤ …` with `h₀` a typing binder.
* `lp2_spatial_strongAMD_safety_source_general`: the same without `hνmax`, `hνle`.

Both are proved from `lp2_spatial_strongAMD_safety` (resp. `…_normalized`); the guards come from its
conclusions.  The planar twin is `lp1_planar_strongAMD_safety_source`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **LP2 through the spatial source carriers, without the normalization premises**
(`LP:MAIN T19 (599–603)`, `L16 (508–529)`). -/
theorem lp2_spatial_strongAMD_safety_source_general (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / spatialKeplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => spatialKeplerAction ν (z t) i) ∈ chamber ν,
              ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
              spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * Real.sqrt μ ∧
            (∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
              |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                  spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
                n * AΛ * Real.sqrt μ) ∧
            (∀ i, dStar ≤ spatialKeplerAxis ν (z t) i *
              (1 - spaceLength (spatialKeplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ spatialKeplerAxis ν (z t) a.upperIdx *
                (1 - spaceLength (spatialKeplerEccVector ν (z t) a.upperIdx)) -
                spatialKeplerAxis ν (z t) a.1 *
                  (1 + spaceLength (spatialKeplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            (∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
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
                      spatialKeplerAxis ν (z t) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialKeplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
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
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1)):= by
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ := lp2_spatial_strongAMD_safety hn ν hν A hA hAord δ γ τ hδ hγ hτ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hdio hch h₀ hC0 T
  obtain ⟨z, hz0, hsol, huniq, hnewt, hall⟩ :=
    H μ hμ hμle z₀ hphys hAz hdio hch hC0
  refine ⟨z, hz0, hsol, huniq, hnewt, fun t ht => ?_⟩
  obtain ⟨hph, ⟨hcht, hamd⟩, hΛ, ha, hdrift, hs1, hs2, hd1, hd2, hosc, hpa, hd3, hd4⟩ :=
    hall t ht
  have hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
      spatialKeplerEnergy ν (z t) i < 0 := fun i => ⟨hν i, hph i⟩
  have ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
      ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
        spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1 :=
    ⟨hν, hμ, fun i => ⟨(hph i).1, (hosc i).1, (hosc i).2.2.1⟩⟩
  exact ⟨hph, ⟨hcht, hs, hamd⟩, hΛ, ha, ⟨hs, hdrift⟩, hs1, hs2, hd1, hd2, ⟨hs, ho, hosc, hpa,
    hd3, hd4⟩⟩

/-- **LP2 through the spatial source carriers, with MAIN's mass normalization** (`hνmax`,
`hνle`; unused premises). -/
theorem lp2_spatial_strongAMD_safety_source (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / spatialKeplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => spatialKeplerAction ν (z t) i) ∈ chamber ν,
              ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
              spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * Real.sqrt μ ∧
            (∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
              |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                  spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
                n * AΛ * Real.sqrt μ) ∧
            (∀ i, dStar ≤ spatialKeplerAxis ν (z t) i *
              (1 - spaceLength (spatialKeplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ spatialKeplerAxis ν (z t) a.upperIdx *
                (1 - spaceLength (spatialKeplerEccVector ν (z t) a.upperIdx)) -
                spatialKeplerAxis ν (z t) a.1 *
                  (1 + spaceLength (spatialKeplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            (∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
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
                      spatialKeplerAxis ν (z t) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialKeplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
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
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1)):= by
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    lp2_spatial_strongAMD_safety_normalized hn ν hν hνmax hνle A hA hAord δ γ τ hδ hγ hτ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hdio hch h₀ hC0 T
  obtain ⟨z, hz0, hsol, huniq, hnewt, hall⟩ :=
    H μ hμ hμle z₀ hphys hAz hdio hch hC0
  refine ⟨z, hz0, hsol, huniq, hnewt, fun t ht => ?_⟩
  obtain ⟨hph, ⟨hcht, hamd⟩, hΛ, ha, hdrift, hs1, hs2, hd1, hd2, hosc, hpa, hd3, hd4⟩ :=
    hall t ht
  have hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
      spatialKeplerEnergy ν (z t) i < 0 := fun i => ⟨hν i, hph i⟩
  have ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
      ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
        spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1 :=
    ⟨hν, hμ, fun i => ⟨(hph i).1, (hosc i).1, (hosc i).2.2.1⟩⟩
  exact ⟨hph, ⟨hcht, hs, hamd⟩, hΛ, ha, ⟨hs, hdrift⟩, hs1, hs2, hd1, hd2, ⟨hs, ho, hosc, hpa,
    hd3, hd4⟩⟩

end KAM.Planetary.Spatial

end
