/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Nek.PlanarSafety.Prograde
public import KAM.Planetary.Newtonian.Reconstruction
public import KAM.Frozen.Planetary.Defs.IsNewtonSolutionOn
public import KAM.Frozen.Planetary.Defs.ActualMasses
public import KAM.Frozen.Planetary.Defs.BarycentricPositions
public import KAM.Frozen.Planetary.Defs.BarycentricVelocities

/-!
# The planar theorem LP3-1 (strong-AMD exponential safety, no arithmetic hypothesis)

Package LP3-PS, MAIN Theorem 15 with Lemma 16, drift from the sealed partial-convexity
Nekhoroshev theorem (`LP:MAIN L14 (468–500)`, `L15 (502–506)`, `L16 (508–529)`;
`LP3-PLAN` §1.2), track LP, non-frozen.

* `lp3_planar_strongAMD_safety`: the text of LP1 (`PlanarSafety/Main`) with the data `γ τ`, the
  premises `hγ hτ` and the Diophantine premise removed, the time `T₀ exp (c μ^{-a_n})` and the drift
  scale `μ^{b_n}` (action, axis and AMD lines) instead of `√μ`.  There is no prograde and no
  arithmetic premise: the orientation is handled by the reflection, as in LP1.
* `lp3_planar_strongAMD_safety_normalized`: the corollary with the unused `hνmax`, `hνle`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

/-- **LP3-1 (planar strong-AMD exponential safety without arithmetic hypothesis;
`LP:MAIN L15 (502–506)` with `L14`, `L16`).** -/
theorem lp3_planar_strongAMD_safety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
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
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * μ ^ planetaryDriftExponent n ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i *
              (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∀ i, oscEnergy ν μ (z t) i < 0 ∧ 0 < oscAxis ν μ (z t) i ∧
                  oscEcc ν μ (z t) i < 1 ∧
                  oscPeri ν μ (z t) i ≤ planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤ oscApo ν μ (z t) i ∧
                  |oscAxis ν μ (z t) i - keplerAxis ν (z t) i| +
                    planeLength (oscEccVector ν μ (z t) i - keplerEccVector ν (z t) i)
                      ≤ Aelem * μ) ∧
            (∀ i, |oscPeri ν μ (z t) i - keplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |oscApo ν μ (z t) i - keplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ oscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤ oscPeri ν μ (z t) a.upperIdx - oscApo ν μ (z t) a.1) := by
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    nek_planar_safety_of_prograde hn ν hν A hA hAord δ hδ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hch hC0 T
  have hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0 :=
    fun i => ⟨hν i, hphys i⟩
  have hC0' : strongAMD ν z₀ ≤ strongThreshold ν (fun i => keplerAction ν z₀ i) - δ := hC0
  -- the total momentum is nonzero (MAIN Lemma 3)
  have hL : totalMomentum z₀ ≠ 0 := by
    refine totalMomentum_ne_zero_of_strongAMD_lt hz (k := ⟨0, by omega⟩) ?_
    have := strongThreshold_le_action ν (fun i => keplerAction ν z₀ i) ⟨0, by omega⟩
    linarith
  have hfin : ∀ z : ℝ → Phase (n * 2),
      nekPlanarSol ν μ (μ ^ planetaryDriftExponent n) T hn δ AΛ Aa dStar dPair Aosc Aelem z₀ z →
      ∃ z : ℝ → Phase (n * 2),
        z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
        MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
        IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
          (fun t => barycentricPositions 1 ν μ (z t).1)
          (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
        ∀ t ∈ Set.Icc (-T) T, nekPlanarState ν μ (μ ^ planetaryDriftExponent n) hn δ AΛ Aa dStar
          dPair Aosc Aelem z₀ (z t) :=
    fun z hz' => ⟨z, hz'.1, hz'.2.1, hz'.2.2.1,
      isNewtonSolutionOn_of_isMovingSolutionOn hν hμ.le hz'.2.1, hz'.2.2.2⟩
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · -- orientation reversal (MAIN Theorem 15, first step)
    have hch' : (fun i => keplerAction ν (reflectPhase z₀) i) ∈ chamber ν := by
      simpa only [keplerAction_reflectPhase] using hch
    obtain ⟨z', hz'⟩ := H μ hμ hμle (reflectPhase z₀)
      (fun i => by
        have := hphys i
        simpa only [planeLength_reflectPhase_fst, keplerEnergy_reflectPhase] using this)
      (by simpa only [keplerAxis_reflectPhase] using hAz)
      (by rw [totalMomentum_reflectPhase]; linarith) hch'
      (by
        show strongAMD ν (reflectPhase z₀) ≤
          strongThreshold ν (fun i => keplerAction ν (reflectPhase z₀) i) - δ
        rw [strongAMD_reflectPhase]
        simpa only [keplerAction_reflectPhase] using hC0')
    exact hfin _ hz'.of_reflectPhase
  · obtain ⟨z, hz'⟩ := H μ hμ hμle z₀ hphys hAz hpos hch hC0
    exact hfin z hz'

/-- LP3-1 with MAIN's mass normalization `max ν = 1` (`hνmax`, `hνle`) as unused premises. -/
theorem lp3_planar_strongAMD_safety_normalized (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (_hνmax : ∃ i, ν i = 1) (_hνle : ∀ i, ν i ≤ 1)
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
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * μ ^ planetaryDriftExponent n ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i *
              (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∀ i, oscEnergy ν μ (z t) i < 0 ∧ 0 < oscAxis ν μ (z t) i ∧
                  oscEcc ν μ (z t) i < 1 ∧
                  oscPeri ν μ (z t) i ≤ planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤ oscApo ν μ (z t) i ∧
                  |oscAxis ν μ (z t) i - keplerAxis ν (z t) i| +
                    planeLength (oscEccVector ν μ (z t) i - keplerEccVector ν (z t) i)
                      ≤ Aelem * μ) ∧
            (∀ i, |oscPeri ν μ (z t) i - keplerPeri ν (z t) i| ≤ Aosc * μ ∧
                  |oscApo ν μ (z t) i - keplerApo ν (z t) i| ≤ Aosc * μ) ∧
            (∀ i, dStar / 2 ≤ oscPeri ν μ (z t) i) ∧
            (∀ a : AdjIdx n, dPair / 2 ≤ oscPeri ν μ (z t) a.upperIdx - oscApo ν μ (z t) a.1) :=
  lp3_planar_strongAMD_safety hn ν hν A hA hAord δ hδ

end KAM.Planetary.StrongAMD

end
