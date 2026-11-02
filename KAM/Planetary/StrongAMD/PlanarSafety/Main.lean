/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.PlanarSafety.Prograde
public import KAM.Planetary.StrongAMD.NonresonantScale
public import KAM.Planetary.Newtonian.Reconstruction
public import KAM.Frozen.Planetary.Defs.IsNewtonSolutionOn
public import KAM.Frozen.Planetary.Defs.ActualMasses
public import KAM.Frozen.Planetary.Defs.BarycentricPositions
public import KAM.Frozen.Planetary.Defs.BarycentricVelocities
public import KAM.Fourier.Derivative

/-!
# The planar theorem LP1 (planar strong-AMD exponential safety)

Source: MAIN Theorem 15 with Lemma 16 (`LP:MAIN T15 (502–506)`, `L14 (468–500)`,
`L16 (508–529)`), track LP, non-frozen.

* `lp1_planar_strongAMD_safety`: the planar statement without the premises `hνmax`, `hνle` (the general version; the anchor keeps them, OD-3).
  Orientation: the total momentum
  is nonzero (MOM), and the case `L < 0` is reduced to `L > 0` by the reflection of
  `PlanarSafety/Orientation`.
* `lp1_planar_strongAMD_safety_normalized`: the corollary with `hνmax`, `hνle`.
* `lp1_planar_strongAMD_safety_halfInteger`: the corollary `τ = n - 1/2` (exponent `1/(2n+1)`).
* `lp0_planar_barrier`: LP0, a restatement of `strongBarrier_physical`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

/-- **LP1 (planar strong-AMD exponential safety; `LP:MAIN T15 (502–506)` with `L14`, `L16`).**
The proposal's statement without `hνmax`, `hνle`. -/
theorem lp1_planar_strongAMD_safety (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
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
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
    planar_safety_of_prograde hn ν hν A hA hAord δ γ τ hδ hγ hτ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hdio hch hC0 T
  have hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0 :=
    fun i => ⟨hν i, hphys i⟩
  have hC0' : strongAMD ν z₀ ≤ strongThreshold ν (fun i => keplerAction ν z₀ i) - δ := hC0
  -- the total momentum is nonzero (MAIN Lemma 3)
  have hL : totalMomentum z₀ ≠ 0 := by
    refine totalMomentum_ne_zero_of_strongAMD_lt hz (k := ⟨0, by omega⟩) ?_
    have := strongThreshold_le_action ν (fun i => keplerAction ν z₀ i) ⟨0, by omega⟩
    linarith
  have hfin : ∀ z : ℝ → Phase (n * 2),
      PlanarSafeSol ν μ T hn δ AΛ Aa dStar dPair Aosc Aelem z₀ z → ∃ z : ℝ → Phase (n * 2),
        z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
        MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
        IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
          (fun t => barycentricPositions 1 ν μ (z t).1)
          (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
        ∀ t ∈ Set.Icc (-T) T, PlanarSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (z t) :=
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
      (by simpa only [keplerAction_reflectPhase] using hdio)
      (by rw [totalMomentum_reflectPhase]; linarith) hch'
      (by
        show strongAMD ν (reflectPhase z₀) ≤
          strongThreshold ν (fun i => keplerAction ν (reflectPhase z₀) i) - δ
        rw [strongAMD_reflectPhase]
        simpa only [keplerAction_reflectPhase] using hC0')
    exact hfin _ hz'.of_reflectPhase
  · obtain ⟨z, hz'⟩ := H μ hμ hμle z₀ hphys hAz hdio hpos hch hC0
    exact hfin z hz'

/-- LP1 with MAIN's mass normalization `max ν = 1` (`hνmax`, `hνle`) as unused premises. -/
theorem lp1_planar_strongAMD_safety_normalized (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (_hνmax : ∃ i, ν i = 1) (_hνle : ∀ i, ν i ≤ 1)
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
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
  lp1_planar_strongAMD_safety hn ν hν A hA hAord δ γ τ hδ hγ hτ

/-- **Corollary `τ = n - 1/2`** (`LP:MAIN §1`): the horizon exponent is `1/(2n+1)`
(`scaleExponent_planar`). -/
theorem lp1_planar_strongAMD_safety_halfInteger (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-((n : ℝ) - 1 / 2)) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
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
              strongAMD ν (z t) ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
            |strongAMD ν (z t) - strongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
  have hτ : (n : ℝ) - 1 < (n : ℝ) - 1 / 2 := by linarith
  have e : 1 / (2 * ((n : ℝ) - 1 / 2 + 1)) = 1 / (2 * (n : ℝ) + 1) :=
    scaleExponent_planar n rfl
  obtain ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, H⟩ :=
    lp1_planar_strongAMD_safety hn ν hν A hA hAord δ γ ((n : ℝ) - 1 / 2) hδ hγ hτ
  refine ⟨μ₀, c, T₀, AΛ, Aa, dStar, dPair, Aosc, Aelem, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, ?_⟩
  intro μ hμ hμle z₀ hphys hAz hdio hch hC0
  have := H μ hμ hμle z₀ hphys hAz hdio hch hC0
  simp only [e] at this
  exact this

/-- **LP0 (planar sharp barrier, full MAIN L5; `LP:MAIN L5 (164)`)**: the source-complete text of
the deficit-list barrier, a compact collision-free set of negative-energy
states, and the physical bounds with the angular-momentum margin and sign.  It is assembled from
`DeficitBarrier`, `exists_barrierCompact` and `strongBarrier_physical`. -/
theorem lp0_planar_barrier (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUch : U ⊆ chamber ν) (m : ℝ) (hm : 0 < m) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      (∀ I : Fin n → ℝ, ∀ hI : I ∈ U, ∀ e : Fin n → ℝ,
        (∀ i, e i ∈ Set.Icc (0 : ℝ) 1) →
        (∑ i, I i * eccDeficit (e i)) ≤ orderedStrongThreshold hn ⟨I, hUch hI⟩ - m →
        (∀ i, dStar ≤ actionAxis ν I i * (1 - e i)) ∧
        (∀ a : AdjIdx n, dPair ≤ actionAxis ν I a.upperIdx * (1 - e a.upperIdx) -
          actionAxis ν I a.1 * (1 + e a.1))) ∧
      ∃ K : Set (Phase (n * 2)), IsCompact K ∧
        (∀ w ∈ K, NoCollision w.1 ∧ ∀ i, keplerEnergy ν w i < 0) ∧
      ∀ z : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) →
        ∀ hΛ : (fun i => keplerAction ν z i) ∈ U,
        strongAMD ν z ≤ orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerAxis ν z a.upperIdx *
            (1 - planeLength (keplerEccVector ν z a.upperIdx)) -
            keplerAxis ν z a.1 * (1 + planeLength (keplerEccVector ν z a.1))) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        z ∈ K ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z) := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, hc, hdef, H⟩ :=
    strongBarrier_physical hν hn hU hUch hm
  obtain ⟨K, hKc, hKsub, hKbar⟩ := exists_barrierCompact hν hn hU hUch hm
  have hcl : IsClosed {x : Fin n → ℝ | ∀ i, x i ≤ -c} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hcont : ContinuousOn (fun w : Phase (n * 2) => fun i => keplerEnergy ν w i) K :=
    continuousOn_pi.2 fun i w hw =>
      (continuousAt_keplerEnergy' ν i ((hKsub hw).1 i)).continuousWithinAt
  have hclK := hcont.preimage_isClosed_of_isClosed hKc.isClosed hcl
  have hKc' := hKc.of_isClosed_subset hclK Set.inter_subset_left
  refine ⟨dS, dP, hdS, hdP, fun I hI e he hsum => hdef I hI e he hsum,
    K ∩ (fun w : Phase (n * 2) => fun i => keplerEnergy ν w i) ⁻¹' {x | ∀ i, x i ≤ -c}, hKc',
    fun w hw => ⟨hKsub hw.1, fun i => lt_of_le_of_lt (hw.2 i) (neg_neg_of_pos hc)⟩,
    fun z hphys hΛ hC => ?_⟩
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := H z ⟨hphys, hΛ, hC⟩
  exact ⟨h1, h2, h3, h4, ⟨hKbar z ⟨hphys, hΛ, hC⟩, h7⟩, h8⟩

end KAM.Planetary.StrongAMD

end
