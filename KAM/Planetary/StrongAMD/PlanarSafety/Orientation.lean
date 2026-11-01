/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Reflection
public import KAM.Planetary.StrongAMD.Osculating
public import KAM.Planetary.StrongAMD.Threshold
public import KAM.Frozen.Planetary.Defs.MovingUniqueOn

/-!
# Orientation reversal of the planar safety conclusion

Package LP-PS (planar theorem LP1, MAIN Theorem 15, `LP:MAIN L15 (502–506)`), track LP, non-frozen.

`PlanarSafeState` is the per-time conjunction of the conclusions of the planar safety theorem
(ellipticity, AMD margin, drifts, separations, osculating clauses) and `PlanarSafeSol` the
solution-level conclusion without the Newtonian reconstruction.  The orientation reversal
`reflectPhase` (LP-MOM) transports both:
`PlanarSafeSol … (reflectPhase z₀) z' → PlanarSafeSol … z₀ (reflectPhase ∘ z')`.
Only invariances are proved here: of `oscVelocity`, `oscEccVector`, `oscPeri`, `oscApo` and of the
moving uniqueness predicate.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

theorem reflectPlane_sum (s : Finset (Fin n)) (f : Fin n → Fin 2 → ℝ) :
    reflectPlane (∑ j ∈ s, f j) = ∑ j ∈ s, reflectPlane (f j) := by
  ext k
  simp only [reflectPlane, Finset.sum_apply]
  split_ifs
  · simp
  · rfl

theorem oscVelocity_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscVelocity ν μ (reflectPhase z) i = reflectPlane (oscVelocity ν μ z i) := by
  unfold oscVelocity
  simp only [bodyVector_reflectPhase_snd, reflectPlane_add, reflectPlane_smul, reflectPlane_sum]

theorem oscEnergy_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscEnergy ν μ (reflectPhase z) i = oscEnergy ν μ z i := by
  unfold oscEnergy
  rw [oscVelocity_reflectPhase, planeSq_reflectPlane, planeLength_reflectPhase_fst]

theorem oscAxis_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscAxis ν μ (reflectPhase z) i = oscAxis ν μ z i := by
  unfold oscAxis
  rw [oscEnergy_reflectPhase]

theorem oscEccVector_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscEccVector ν μ (reflectPhase z) i = reflectPlane (oscEccVector ν μ z i) := by
  unfold oscEccVector
  simp only [oscVelocity_reflectPhase, bodyVector_reflectPhase_fst, planeSq_reflectPlane,
    planeLength_reflectPlane, planeDot_reflectPlane, reflectPlane_sub, reflectPlane_smul]

theorem oscEcc_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscEcc ν μ (reflectPhase z) i = oscEcc ν μ z i := by
  unfold oscEcc
  rw [oscEccVector_reflectPhase, planeLength_reflectPlane]

theorem oscPeri_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscPeri ν μ (reflectPhase z) i = oscPeri ν μ z i := by
  unfold oscPeri
  rw [oscAxis_reflectPhase, oscEcc_reflectPhase]

theorem oscApo_reflectPhase (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscApo ν μ (reflectPhase z) i = oscApo ν μ z i := by
  unfold oscApo
  rw [oscAxis_reflectPhase, oscEcc_reflectPhase]

theorem keplerPeri_reflectPhase (ν : Fin n → ℝ) (z : Phase (n * 2)) (i : Fin n) :
    keplerPeri ν (reflectPhase z) i = keplerPeri ν z i := by
  unfold keplerPeri
  rw [keplerAxis_reflectPhase, planeLength_keplerEccVector_reflectPhase]

theorem keplerApo_reflectPhase (ν : Fin n → ℝ) (z : Phase (n * 2)) (i : Fin n) :
    keplerApo ν (reflectPhase z) i = keplerApo ν z i := by
  unfold keplerApo
  rw [keplerAxis_reflectPhase, planeLength_keplerEccVector_reflectPhase]

/-- The action vector is invariant under orientation reversal. -/
theorem actionVector_reflectPhase (ν : Fin n → ℝ) (z : Phase (n * 2)) :
    actionVector ν (reflectPhase z) = actionVector ν z :=
  funext fun i => keplerAction_reflectPhase ν z i

/-- The per-time conclusions of the planar safety theorem at a state `zt`, relative to the initial
state `z₀` (`LP:MAIN L15 (502–506)`, `L16`; the clauses of the proposal's LP1 in the order
written there). -/
def PlanarSafeState (ν : Fin n → ℝ) (μ : ℝ) (hn : 2 ≤ n) (δ AΛ Aa dStar dPair Aosc Aelem : ℝ)
    (z₀ zt : Phase (n * 2)) : Prop :=
  (∀ i, 0 < planeLength (bodyVector zt.1 i) ∧ keplerEnergy ν zt i < 0) ∧
  (∃ hcht : (fun i => keplerAction ν zt i) ∈ chamber ν,
    strongAMD ν zt ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
  ‖(fun i => keplerAction ν zt i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
  ‖(fun i => keplerAxis ν zt i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
  |strongAMD ν zt - strongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
  (∀ i, dStar ≤ keplerAxis ν zt i * (1 - planeLength (keplerEccVector ν zt i))) ∧
  (∀ a : AdjIdx n, dPair ≤ keplerAxis ν zt a.upperIdx *
      (1 - planeLength (keplerEccVector ν zt a.upperIdx)) -
      keplerAxis ν zt a.1 * (1 + planeLength (keplerEccVector ν zt a.1))) ∧
  (∀ i, dStar ≤ planeLength (bodyVector zt.1 i)) ∧
  (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector zt.1 i - bodyVector zt.1 j)) ∧
  (∀ i, oscEnergy ν μ zt i < 0 ∧ 0 < oscAxis ν μ zt i ∧ oscEcc ν μ zt i < 1 ∧
      oscPeri ν μ zt i ≤ planeLength (bodyVector zt.1 i) ∧
      planeLength (bodyVector zt.1 i) ≤ oscApo ν μ zt i ∧
      |oscAxis ν μ zt i - keplerAxis ν zt i| +
        planeLength (oscEccVector ν μ zt i - keplerEccVector ν zt i) ≤ Aelem * μ) ∧
  (∀ i, |oscPeri ν μ zt i - keplerPeri ν zt i| ≤ Aosc * μ ∧
        |oscApo ν μ zt i - keplerApo ν zt i| ≤ Aosc * μ) ∧
  (∀ i, dStar / 2 ≤ oscPeri ν μ zt i) ∧
  (∀ a : AdjIdx n, dPair / 2 ≤ oscPeri ν μ zt a.upperIdx - oscApo ν μ zt a.1)

/-- The solution-level conclusion (existence data, uniqueness, and the per-time clauses), without
the Newtonian reconstruction. -/
def PlanarSafeSol (ν : Fin n → ℝ) (μ T : ℝ) (hn : 2 ≤ n) (δ AΛ Aa dStar dPair Aosc Aelem : ℝ)
    (z₀ : Phase (n * 2)) (z : ℝ → Phase (n * 2)) : Prop :=
  z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Icc (-T) T) z ∧ MovingUniqueOn ν μ (Icc (-T) T) z ∧
    ∀ t ∈ Icc (-T) T, PlanarSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (z t)

theorem PlanarSafeState.of_reflectPhase {ν : Fin n → ℝ} {μ : ℝ} {hn : 2 ≤ n}
    {δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ zt : Phase (n * 2)}
    (h : PlanarSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem (reflectPhase z₀)
      (reflectPhase zt)) :
    PlanarSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem z₀ zt := by
  obtain ⟨h1, ⟨hch, h2⟩, h3, h4, h5, h6, h7, h8, h9, hv, h10, h11, h12⟩ := h
  have hact : ∀ w : Phase (n * 2), (fun i => keplerAction ν (reflectPhase w) i) =
      fun i => keplerAction ν w i := fun w => actionVector_reflectPhase ν w
  simp only [hact, strongAMD_reflectPhase, keplerEnergy_reflectPhase,
    planeLength_reflectPhase_fst, planeLength_reflectPhase_sub,
    planeLength_keplerEccVector_reflectPhase, keplerAxis_reflectPhase] at h1 h3 h4 h5 h6 h7 h8 h9
  simp only [oscPeri_reflectPhase, oscApo_reflectPhase, keplerPeri_reflectPhase,
    keplerApo_reflectPhase] at h10 h11 h12
  simp only [oscEnergy_reflectPhase, oscAxis_reflectPhase, oscEcc_reflectPhase,
    oscPeri_reflectPhase, oscApo_reflectPhase, planeLength_reflectPhase_fst,
    keplerAxis_reflectPhase, oscEccVector_reflectPhase, keplerEccVector_reflectPhase,
    ← reflectPlane_sub, planeLength_reflectPlane] at hv
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h8, h9, hv, h10, h11, h12⟩
  refine ⟨(hact zt) ▸ hch, ?_⟩
  have h2' : strongAMD ν (reflectPhase zt) ≤
      strongThreshold ν (fun i => keplerAction ν (reflectPhase zt) i) - δ / 2 := h2
  rw [hact zt, strongAMD_reflectPhase] at h2'
  exact h2'

/-- Orientation reversal transports the solution-level conclusion. -/
theorem PlanarSafeSol.of_reflectPhase {ν : Fin n → ℝ} {μ T : ℝ} {hn : 2 ≤ n}
    {δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ : Phase (n * 2)} {z' : ℝ → Phase (n * 2)}
    (h : PlanarSafeSol ν μ T hn δ AΛ Aa dStar dPair Aosc Aelem (reflectPhase z₀) z') :
    PlanarSafeSol ν μ T hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (fun t => reflectPhase (z' t)) := by
  obtain ⟨h0, hsol, huniq, hst⟩ := h
  refine ⟨by simp [h0, reflectPhase_reflectPhase], isMovingSolutionOn_reflectPhase_of hsol, ?_,
    fun t ht => ?_⟩
  · intro U w hU hconv h0U hw0 hwsol t ht
    have hw' := isMovingSolutionOn_reflectPhase_of hwsol
    have := huniq U (fun t => reflectPhase (w t)) hU hconv h0U
      (by simp only [hw0, h0, reflectPhase_reflectPhase])
      hw' t ht
    have h2 := congrArg reflectPhase this
    simpa [reflectPhase_reflectPhase] using h2
  · have := hst t ht
    refine PlanarSafeState.of_reflectPhase ?_
    simpa [reflectPhase_reflectPhase] using this

end KAM.Planetary.StrongAMD

end
