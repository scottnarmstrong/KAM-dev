/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.SpatialSafety.Aligned
public import KAM.Planetary.Spatial.Newton

/-!
# The spatial theorem LP2 (spatial strong-AMD exponential safety)

Source: MAIN Theorem 19 with Lemma 16 for `d = 3` (`LP:MAIN T19 (599–603)`,
`L14 (468–500)`, `L16 (508–529)`, `L18 (595–597)`), track LP, non-frozen.

* `lp2_spatial_strongAMD_safety`: the spatial twin of `lp1_planar_strongAMD_safety` (the planar
  statement without `hνmax`, `hνle`), with
  `Phase (n * 3)`, `bodyVector3`, `spaceLength`, the spatial Kepler elements, `spatialStrongAMD`
  (Euclidean `|L|`), `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn`,
  `IsSpatialNewtonSolutionOn` and the spatial osculating elements.  The premises are exactly those
  of LP1: no prograde, small-inclination, nonzero-total-angular-momentum, secular-confinement or
  alignment premise.  Orientation: the total angular momentum is nonzero (Lemma 3, `L ≠ 0` from
  the AMD level), and a rotation aligns it with `e₃` (`SpatialSafety/Orientation`).
* `lp2_spatial_strongAMD_safety_normalized`: the corollary with `hνmax`, `hνle` (unused).
* `lp2_spatial_strongAMD_safety_halfInteger`: the corollary `τ = n - 1/2` (exponent `1/(2n+1)`).

-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **LP2 (spatial strong-AMD exponential safety; `LP:MAIN T19 (599–603)` with `L14`, `L16`,
`L18`).**  The spatial twin of `lp1_planar_strongAMD_safety`: the statement of LP1 for `d = 3`
without `hνmax`, `hνle`, and with no orientation premise. -/
theorem lp2_spatial_strongAMD_safety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
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
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              spatialStrongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialStrongAMD ν (z t) - spatialStrongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
    spatial_safety_of_aligned hn ν hν A hA hAord δ γ τ hδ hγ hτ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hdio hch hC0 T
  have hz : SpatialNegativeEnergy ν z₀ := fun i => ⟨hν i, hphys i⟩
  have hC0' : spatialStrongAMD ν z₀ ≤ strongThreshold ν (fun i => spatialKeplerAction ν z₀ i) - δ :=
    hC0
  -- the total angular momentum is nonzero (MAIN Lemma 3)
  have hL : angularMomentum3 z₀ ≠ 0 := by
    refine angularMomentum3_ne_zero_of_strongAMD_lt hz (k := ⟨0, by omega⟩) ?_
    have := strongThreshold_le_action ν (fun i => spatialKeplerAction ν z₀ i) ⟨0, by omega⟩
    linarith
  have hfin : ∀ z : ℝ → Phase (n * 3),
      SpatialSafeSol ν μ T hn δ AΛ Aa dStar dPair Aosc Aelem z₀ z → ∃ z : ℝ → Phase (n * 3),
        z 0 = z₀ ∧ IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
        SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
        IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
          (fun t => spatialBarycentricPositions ν μ (z t).1)
          (fun t => spatialBarycentricVelocities ν μ (z t).2) ∧
        ∀ t ∈ Set.Icc (-T) T,
          SpatialSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (z t) :=
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
    (by simpa only [spatialKeplerAction_rotate hR] using hdio) hal hch'
    (by
      show spatialStrongAMD ν (spatialRotatePhase R z₀) ≤
        strongThreshold ν (fun i => spatialKeplerAction ν (spatialRotatePhase R z₀) i) - δ
      rw [spatialStrongAMD_rotate hR hdet]
      simpa only [spatialKeplerAction_rotate hR] using hC0')
  exact hfin _ (hz'.of_rotate hR hdet)

/-- LP2 with MAIN's mass normalization `max ν = 1` (`hνmax`, `hνle`) as unused premises: the
spatial twin of `lp1_planar_strongAMD_safety_normalized`. -/
theorem lp2_spatial_strongAMD_safety_normalized (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (_hνmax : ∃ i, ν i = 1) (_hνle : ∀ i, ν i ≤ 1)
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
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              spatialStrongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialStrongAMD ν (z t) - spatialStrongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
  lp2_spatial_strongAMD_safety hn ν hν A hA hAord δ γ τ hδ hγ hτ

/-- **Corollary `τ = n - 1/2`** (`LP:MAIN §1`): the horizon exponent is `1/(2n+1)`. -/
theorem lp2_spatial_strongAMD_safety_halfInteger (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-((n : ℝ) - 1 / 2)) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / spatialKeplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (n : ℝ) + 1))))
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
              AΛ * Real.sqrt μ ∧
            ‖(fun i => spatialKeplerAxis ν (z t) i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
              Aa * Real.sqrt μ ∧
            |spatialStrongAMD ν (z t) - spatialStrongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
  have hτ : (n : ℝ) - 1 < (n : ℝ) - 1 / 2 := by linarith
  have e : 1 / (2 * ((n : ℝ) - 1 / 2 + 1)) = 1 / (2 * (n : ℝ) + 1) := by
    congr 1; ring
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    lp2_spatial_strongAMD_safety hn ν hν A hA hAord δ γ ((n : ℝ) - 1 / 2) hδ hγ hτ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hdio hch hC0
  have := H μ hμ hμle z₀ hphys hAz hdio hch hC0
  simp only [e] at this
  exact this

end KAM.Planetary.Spatial

end
