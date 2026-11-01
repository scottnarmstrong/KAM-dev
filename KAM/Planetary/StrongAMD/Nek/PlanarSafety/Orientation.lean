/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.PlanarSafety.Orientation

/-!
# Orientation reversal of the LP3 planar safety conclusion (drift scale as a parameter)

Package LP3-PS (planar theorem LP3-1, `LP:MAIN L14 (468–500)`, `L15 (502–506)`, `L16 (508–529)`),
track LP, non-frozen.

`nekPlanarState` and `nekPlanarSol` are the per-time and solution-level conclusions of LP3-1.  They
are the LP1 predicates `PlanarSafeState`, `PlanarSafeSol` with the hard-coded drift scale `√μ`
replaced by a parameter `s` (in LP3-1: `s = μ ^ b_n`).  The reflection `reflectPhase` transports
both (the invariance lemmas are those of `PlanarSafety/Orientation`).

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

/-- The per-time conclusions of LP3-1 at `zt` relative to `z₀`, with drift scale `s`
(`LP:MAIN L15 (502–506)`, `L16`). -/
def nekPlanarState (ν : Fin n → ℝ) (μ s : ℝ) (hn : 2 ≤ n)
    (δ AΛ Aa dStar dPair Aosc Aelem : ℝ) (z₀ zt : Phase (n * 2)) : Prop :=
  (∀ i, 0 < planeLength (bodyVector zt.1 i) ∧ keplerEnergy ν zt i < 0) ∧
  (∃ hcht : (fun i => keplerAction ν zt i) ∈ chamber ν,
    strongAMD ν zt ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
  ‖(fun i => keplerAction ν zt i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * s ∧
  ‖(fun i => keplerAxis ν zt i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * s ∧
  |strongAMD ν zt - strongAMD ν z₀| ≤ n * AΛ * s ∧
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

/-- The solution-level conclusion of LP3-1 without the Newtonian reconstruction. -/
def nekPlanarSol (ν : Fin n → ℝ) (μ s T : ℝ) (hn : 2 ≤ n)
    (δ AΛ Aa dStar dPair Aosc Aelem : ℝ) (z₀ : Phase (n * 2)) (z : ℝ → Phase (n * 2)) : Prop :=
  z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Icc (-T) T) z ∧ MovingUniqueOn ν μ (Icc (-T) T) z ∧
    ∀ t ∈ Icc (-T) T, nekPlanarState ν μ s hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (z t)

theorem nekPlanarState.of_reflectPhase {ν : Fin n → ℝ} {μ s : ℝ} {hn : 2 ≤ n}
    {δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ zt : Phase (n * 2)}
    (h : nekPlanarState ν μ s hn δ AΛ Aa dStar dPair Aosc Aelem (reflectPhase z₀)
      (reflectPhase zt)) :
    nekPlanarState ν μ s hn δ AΛ Aa dStar dPair Aosc Aelem z₀ zt := by
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

/-- Orientation reversal transports the solution-level conclusion of LP3-1. -/
theorem nekPlanarSol.of_reflectPhase {ν : Fin n → ℝ} {μ s T : ℝ} {hn : 2 ≤ n}
    {δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ : Phase (n * 2)} {z' : ℝ → Phase (n * 2)}
    (h : nekPlanarSol ν μ s T hn δ AΛ Aa dStar dPair Aosc Aelem (reflectPhase z₀) z') :
    nekPlanarSol ν μ s T hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (fun t => reflectPhase (z' t)) := by
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
    refine nekPlanarState.of_reflectPhase ?_
    simpa [reflectPhase_reflectPhase] using this

end KAM.Planetary.StrongAMD

end
