/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.PlanarSafety.Source
public import KAM.Planetary.StrongAMD.NonresonantScale

/-!
# LP0 and the `τ = n - 1/2` corollary of LP1 through the source carriers (OD-11 (b))

Package LP-FREEZE7 (`LP:MAIN L5 (162–166)`, `§1 (93)`, `L15 (502–506)`, `L16 (508–529)`), track LP,
non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

* `lp0_planar_barrier_source`: the LP0 text (full MAIN L5; statement review 1, F1) in which the
  strong AMD of the physical state is `sourceStrongAMD ⟨z, h⟩` on the source carrier
  `SourceCanonicalPhase n ν`, with `h` a typing binder (exactly as §3b did for LP1). Proved from
  `lp0_planar_barrier` (definitional repacking).
* `lp1_planar_strongAMD_safety_source_halfInteger`: `lp1_planar_strongAMD_safety_source` at
  `τ = n - 1/2`, with the horizon exponent written explicitly as `1/(2n+1)` (MAIN §1, line 93).
  Proved from `lp1_planar_strongAMD_safety_source` and `scaleExponent_planar`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary

/-- **LP0 through the source carrier** (`LP:MAIN L5 (162–166)`): the full sharp barrier, with the
strong AMD of the physical state on `SourceCanonicalPhase n ν`. -/
theorem lp0_planar_barrier_source {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
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
        ∀ h : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0,
        sourceStrongAMD (⟨z, h⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - m →
        (∀ i, dStar ≤ keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i))) ∧
        (∀ a : AdjIdx n, dPair ≤ keplerAxis ν z a.upperIdx *
            (1 - planeLength (keplerEccVector ν z a.upperIdx)) -
            keplerAxis ν z a.1 * (1 + planeLength (keplerEccVector ν z a.1))) ∧
        (∀ i, dStar ≤ planeLength (bodyVector z.1 i)) ∧
        (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)) ∧
        z ∈ K ∧
        (∀ i, m ≤ |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ∧
          0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) * totalMomentum z) := by
  obtain ⟨dS, dP, hdS, hdP, hdef, K, hK, hKs, H⟩ := lp0_planar_barrier hn ν hν U hU hUch m hm
  exact ⟨dS, dP, hdS, hdP, hdef, K, hK, hKs, fun z hphys hΛ _h hC => H z hphys hΛ hC⟩

/-- **LP1 at `τ = n - 1/2` through the source carriers** (`LP:MAIN §1 (93)`, `L15 (502–506)`): the
horizon is `T₀ exp (c μ^(-1/(2n+1)))`. -/
theorem lp1_planar_strongAMD_safety_source_halfInteger {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
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
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-((n : ℝ) - 1 / 2)) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
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
  have hτ : (n : ℝ) - 1 < (n : ℝ) - 1 / 2 := by linarith
  have e : 1 / (2 * ((n : ℝ) - 1 / 2 + 1)) = 1 / (2 * (n : ℝ) + 1) :=
    scaleExponent_planar n rfl
  have H := lp1_planar_strongAMD_safety_source hn ν hν hνmax hνle A hA hAord δ γ ((n : ℝ) - 1 / 2)
    hδ hγ hτ
  rw [e] at H
  exact H

end KAM.Planetary.StrongAMD
