/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Nek.SpatialSafety.Aligned
public import KAM.Planetary.Spatial.Newton

/-!
# The spatial theorem the Nekhoroshev part (spatial strong-AMD exponential safety, no arithmetic
hypothesis)

Source: `LP:MAIN T19 (599–603)` with `L14 (468–500)`, `L16 (508–529)`,
`L18 (595–597)` for `d = 3`, track LP, non-frozen.

* `lp3_spatial_strongAMD_safety`: the text of `lp2_spatial_strongAMD_safety` with exactly three
  changes: the data `γ τ`, the premises `hγ hτ` and the Diophantine premise are removed; the time
  is `T₀ * exp (c * μ ^ (-planetaryTimeExponent n))`; the drift lines read
  `μ ^ planetaryDriftExponent n` instead of `√μ`.  No prograde, small-inclination,
  nonzero-angular-momentum, secular-confinement, alignment or arithmetic premise.
* `lp3_spatial_strongAMD_safety_normalized`: the corollary with `hνmax`, `hνle` (unused).

-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **The Nekhoroshev part (spatial strong-AMD exponential safety, no arithmetic hypothesis;
`LP:MAIN T19 (599–603)` with `L14 (468–500)`, `L16`, `L18`).**  The statement of
`lp2_spatial_strongAMD_safety` without `γ τ` and the Diophantine premise, with time
`T₀ exp (c μ^{-a_n})` and drift scale `μ^{b_n}`; no orientation premise. -/
theorem lp3_spatial_strongAMD_safety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => spatialKeplerAction ν (z t) i) ∈ chamber ν,
              spatialStrongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |spatialStrongAMD ν (z t) - spatialStrongAMD ν z₀| ≤
              n * AΛ * μ ^ planetaryDriftExponent n ∧
            (∀ i, dStar ≤ spatialKeplerAxis ν (z t) i *
              (1 - spaceLength (spatialKeplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ spatialKeplerAxis ν (z t) a.upperIdx *
                (1 - spaceLength (spatialKeplerEccVector ν (z t) a.upperIdx)) -
                spatialKeplerAxis ν (z t) a.1 *
                  (1 + spaceLength (spatialKeplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            (∀ i, spatialOscEnergy ν μ (z t) i < 0 ∧ 0 < spatialOscAxis ν μ (z t) i ∧
                  spatialOscEcc ν μ (z t) i < 1 ∧
                  spatialOscPeri ν μ (z t) i ≤ spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤ spatialOscApo ν μ (z t) i ∧
                  |spatialOscAxis ν μ (z t) i - spatialKeplerAxis ν (z t) i| +
                    spaceLength (spatialOscEccVector ν μ (z t) i -
                      spatialKeplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
            (∀ i, |spatialOscPeri ν μ (z t) i - spatialKeplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |spatialOscApo ν μ (z t) i - spatialKeplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ spatialOscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤
              spatialOscPeri ν μ (z t) a.upperIdx - spatialOscApo ν μ (z t) a.1) := by
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    spatial_nek_safety_of_aligned hn ν hν A hA hAord δ hδ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hch hC0 T
  have hz : SpatialNegativeEnergy ν z₀ := fun i => ⟨hν i, hphys i⟩
  have hC0' : spatialStrongAMD ν z₀ ≤ strongThreshold ν (fun i => spatialKeplerAction ν z₀ i) - δ :=
    hC0
  -- the total angular momentum is nonzero (MAIN Lemma 3)
  have hL : angularMomentum3 z₀ ≠ 0 := by
    refine angularMomentum3_ne_zero_of_strongAMD_lt hz (k := ⟨0, by omega⟩) ?_
    have := strongThreshold_le_action ν (fun i => spatialKeplerAction ν z₀ i) ⟨0, by omega⟩
    linarith
  have hfin : ∀ z : ℝ → Phase (n * 3),
      SpatialNekSafeSol ν μ T hn (μ ^ planetaryDriftExponent n) δ AΛ Aa dStar dPair Aosc
        Aelem z₀ z → ∃ z : ℝ → Phase (n * 3),
        z 0 = z₀ ∧ IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
        SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
        IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
          (fun t => spatialBarycentricPositions ν μ (z t).1)
          (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
        ∀ t ∈ Set.Icc (-T) T,
          SpatialNekSafeState ν μ hn (μ ^ planetaryDriftExponent n) δ AΛ Aa dStar dPair Aosc
            Aelem z₀ (z t) :=
    fun z hz' => ⟨z, hz'.1, hz'.2.1, hz'.2.2.1,
      isSpatialNewtonSolutionOn_of_isSpatialMovingSolutionOn hν hμ.le hz'.2.1, hz'.2.2.2⟩
  -- rotation alignment of `L` with `e₃` (MAIN Lemma 18)
  obtain ⟨R, hR, hdet, hRu⟩ := exists_rotation_align_angularMomentum3 hL
  have hpos : 0 < spaceLength (angularMomentum3 (spatialRotatePhase R z₀)) := by
    rw [angularMomentum3_rotate hR hdet, spaceLength_mulVec hR]
    exact spaceLength_pos_iff.2 hL
  have hal : angularMomentum3 (spatialRotatePhase R z₀) =
      spaceLength (angularMomentum3 (spatialRotatePhase R z₀)) • e₃ := by
    have hu : (spaceLength (angularMomentum3 (spatialRotatePhase R z₀)))⁻¹ •
        angularMomentum3 (spatialRotatePhase R z₀) = e₃ := hRu
    calc angularMomentum3 (spatialRotatePhase R z₀)
        = spaceLength (angularMomentum3 (spatialRotatePhase R z₀)) •
            ((spaceLength (angularMomentum3 (spatialRotatePhase R z₀)))⁻¹ •
              angularMomentum3 (spatialRotatePhase R z₀)) := by
          rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      _ = _ := by rw [hu]
  have hch' : (fun i => spatialKeplerAction ν (spatialRotatePhase R z₀) i) ∈ chamber ν := by
    simpa only [spatialKeplerAction_rotate hR] using hch
  obtain ⟨z', hz'⟩ := H μ hμ hμle (spatialRotatePhase R z₀)
    (fun i => by
      have := hphys i
      simpa only [spaceLength_bodyVector3_rotate hR, spatialKeplerEnergy_rotate hR] using this)
    (by simpa only [spatialKeplerAxis_rotate hR] using hAz)
    hal hch'
    (by
      show spatialStrongAMD ν (spatialRotatePhase R z₀) ≤
        strongThreshold ν (fun i => spatialKeplerAction ν (spatialRotatePhase R z₀) i) - δ
      rw [spatialStrongAMD_rotate hR hdet]
      simpa only [spatialKeplerAction_rotate hR] using hC0')
  exact hfin _ (hz'.transport_rotate hR hdet)

/-- The Nekhoroshev part with MAIN's mass normalization `max ν = 1` (`hνmax`, `hνle`) as unused
premises: the spatial twin of `lp3_planar_strongAMD_safety_normalized`. -/
theorem lp3_spatial_strongAMD_safety_normalized (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (_hνmax : ∃ i, ν i = 1) (_hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialBarycentricPositions ν μ (z t).1)
            (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧ spatialKeplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => spatialKeplerAction ν (z t) i) ∈ chamber ν,
              spatialStrongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |spatialStrongAMD ν (z t) - spatialStrongAMD ν z₀| ≤
              n * AΛ * μ ^ planetaryDriftExponent n ∧
            (∀ i, dStar ≤ spatialKeplerAxis ν (z t) i *
              (1 - spaceLength (spatialKeplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ spatialKeplerAxis ν (z t) a.upperIdx *
                (1 - spaceLength (spatialKeplerEccVector ν (z t) a.upperIdx)) -
                spatialKeplerAxis ν (z t) a.1 *
                  (1 + spaceLength (spatialKeplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            (∀ i, spatialOscEnergy ν μ (z t) i < 0 ∧ 0 < spatialOscAxis ν μ (z t) i ∧
                  spatialOscEcc ν μ (z t) i < 1 ∧
                  spatialOscPeri ν μ (z t) i ≤ spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤ spatialOscApo ν μ (z t) i ∧
                  |spatialOscAxis ν μ (z t) i - spatialKeplerAxis ν (z t) i| +
                    spaceLength (spatialOscEccVector ν μ (z t) i -
                      spatialKeplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
            (∀ i, |spatialOscPeri ν μ (z t) i - spatialKeplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |spatialOscApo ν μ (z t) i - spatialKeplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ spatialOscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤
              spatialOscPeri ν μ (z t) a.upperIdx - spatialOscApo ν μ (z t) a.1) :=
  lp3_spatial_strongAMD_safety hn ν hν A hA hAord δ hδ

end KAM.Planetary.Spatial

end
