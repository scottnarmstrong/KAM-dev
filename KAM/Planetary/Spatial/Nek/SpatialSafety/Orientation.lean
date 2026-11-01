/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.SpatialSafety.Orientation

/-!
# Drift-scale-generic safe states and their rotation transport (LP3-SP-SAFE)

Package LP3-SP-SAFE (spatial theorem LP3-2, `LP:MAIN T19 (599–603)`, `L16 (508–529)`,
`L18 (595–597)`), track LP, non-frozen.  `SpatialNekSafeState`/`SpatialNekSafeSol` are the LP2
predicates `SpatialSafeState`/`SpatialSafeSol` with the hard-coded drift scale `√μ` replaced by a
parameter `ρ` (for LP3, `ρ = μ ^ planetaryDriftExponent n`); `transport_rotate` is the same
proof.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Matrix

variable {n : ℕ} {R : Matrix (Fin 3) (Fin 3) ℝ}

/-- Drift-scale-generic per-time conclusions of the spatial safety theorem (drift scale `ρ`:
`ρ = μ ^ b_n` for LP3, `ρ = √μ` for LP2) at a state `zt`, relative to the
initial state `z₀` (`LP:MAIN T19 (599–603)`, `L16`; the clauses of LP1 in the order written
there, with `d = 3`). -/
def SpatialNekSafeState (ν : Fin n → ℝ) (μ : ℝ) (hn : 2 ≤ n)
    (ρ δ AΛ Aa dStar dPair Aosc Aelem : ℝ) (z₀ zt : Phase (n * 3)) : Prop :=
  (∀ i, 0 < spaceLength (bodyVector3 zt.1 i) ∧ spatialKeplerEnergy ν zt i < 0) ∧
  (∃ hcht : (fun i => spatialKeplerAction ν zt i) ∈ chamber ν,
    spatialStrongAMD ν zt ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
  ‖(fun i => spatialKeplerAction ν zt i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
    AΛ * ρ ∧
  ‖(fun i => spatialKeplerAxis ν zt i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
    Aa * ρ ∧
  |spatialStrongAMD ν zt - spatialStrongAMD ν z₀| ≤ n * AΛ * ρ ∧
  (∀ i, dStar ≤ spatialKeplerAxis ν zt i * (1 - spaceLength (spatialKeplerEccVector ν zt i))) ∧
  (∀ a : AdjIdx n, dPair ≤ spatialKeplerAxis ν zt a.upperIdx *
      (1 - spaceLength (spatialKeplerEccVector ν zt a.upperIdx)) -
      spatialKeplerAxis ν zt a.1 * (1 + spaceLength (spatialKeplerEccVector ν zt a.1))) ∧
  (∀ i, dStar ≤ spaceLength (bodyVector3 zt.1 i)) ∧
  (∀ i j, i ≠ j → dPair ≤ spaceLength (bodyVector3 zt.1 i - bodyVector3 zt.1 j)) ∧
  (∀ i, spatialOscEnergy ν μ zt i < 0 ∧ 0 < spatialOscAxis ν μ zt i ∧
      spatialOscEcc ν μ zt i < 1 ∧
      spatialOscPeri ν μ zt i ≤ spaceLength (bodyVector3 zt.1 i) ∧
      spaceLength (bodyVector3 zt.1 i) ≤ spatialOscApo ν μ zt i ∧
      |spatialOscAxis ν μ zt i - spatialKeplerAxis ν zt i| +
        spaceLength (spatialOscEccVector ν μ zt i - spatialKeplerEccVector ν zt i) ≤
          Aelem * μ) ∧
  (∀ i, |spatialOscPeri ν μ zt i - spatialKeplerPeri ν zt i| ≤ Aosc * μ ∧
        |spatialOscApo ν μ zt i - spatialKeplerApo ν zt i| ≤ Aosc * μ) ∧
  (∀ i, dStar / 2 ≤ spatialOscPeri ν μ zt i) ∧
  (∀ a : AdjIdx n, dPair / 2 ≤ spatialOscPeri ν μ zt a.upperIdx - spatialOscApo ν μ zt a.1)

/-- The solution-level conclusion (existence data, uniqueness, and the per-time clauses),
without the Newtonian reconstruction. -/
def SpatialNekSafeSol (ν : Fin n → ℝ) (μ T : ℝ) (hn : 2 ≤ n)
    (ρ δ AΛ Aa dStar dPair Aosc Aelem : ℝ) (z₀ : Phase (n * 3)) (z : ℝ → Phase (n * 3)) : Prop :=
  z 0 = z₀ ∧ IsSpatialMovingSolutionOn ν μ (Icc (-T) T) z ∧
    SpatialMovingUniqueOn ν μ (Icc (-T) T) z ∧
    ∀ t ∈ Icc (-T) T, SpatialNekSafeState ν μ hn ρ δ AΛ Aa dStar dPair Aosc Aelem z₀ (z t)

/-- Rotation transports the per-time conclusion back: if the state `R zt` satisfies the
conclusions relative to `R z₀`, then `zt` satisfies them relative to `z₀`. -/
theorem SpatialNekSafeState.transport_rotate (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    {ν : Fin n → ℝ} {μ : ℝ}
    {hn : 2 ≤ n} {ρ δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ zt : Phase (n * 3)}
    (h : SpatialNekSafeState ν μ hn ρ δ AΛ Aa dStar dPair Aosc Aelem (spatialRotatePhase R z₀)
      (spatialRotatePhase R zt)) :
    SpatialNekSafeState ν μ hn ρ δ AΛ Aa dStar dPair Aosc Aelem z₀ zt := by
  obtain ⟨h1, ⟨hch, h2⟩, h3, h4, h5, h6, h7, h8, h9, hv, h10, h11, h12⟩ := h
  have hact : ∀ w : Phase (n * 3), (fun i => spatialKeplerAction ν (spatialRotatePhase R w) i) =
      fun i => spatialKeplerAction ν w i := fun w => spatialActionVector_rotate hR ν w
  simp only [hact, spatialStrongAMD_rotate hR hdet, spatialKeplerEnergy_rotate hR,
    spaceLength_bodyVector3_rotate hR, spaceLength_bodyVector3_rotate_sub hR,
    spaceLength_spatialKeplerEccVector_rotate hR, spatialKeplerAxis_rotate hR]
    at h1 h3 h4 h5 h6 h7 h8 h9
  simp only [spatialOscPeri_rotate hR, spatialOscApo_rotate hR, spatialKeplerPeri_rotate hR,
    spatialKeplerApo_rotate hR] at h10 h11 h12
  simp only [spatialOscEnergy_rotate hR, spatialOscAxis_rotate hR, spatialOscEcc_rotate hR,
    spatialOscPeri_rotate hR, spatialOscApo_rotate hR, spaceLength_bodyVector3_rotate hR,
    spatialKeplerAxis_rotate hR, spaceLength_oscEccVector_sub_rotate hR] at hv
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, h8, h9, hv, h10, h11, h12⟩
  refine ⟨(hact zt) ▸ hch, ?_⟩
  have h2' : spatialStrongAMD ν (spatialRotatePhase R zt) ≤
      strongThreshold ν (fun i => spatialKeplerAction ν (spatialRotatePhase R zt) i) - δ / 2 :=
    h2
  rw [hact zt, spatialStrongAMD_rotate hR hdet] at h2'
  exact h2'

/-- Rotation transports the solution-level conclusion: a solution starting at `R z₀` is
rotated back by `Rᵀ` to one starting at `z₀`. -/
theorem SpatialNekSafeSol.transport_rotate (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    {ν : Fin n → ℝ} {μ T : ℝ}
    {hn : 2 ≤ n} {ρ δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ : Phase (n * 3)}
    {z' : ℝ → Phase (n * 3)}
    (h : SpatialNekSafeSol ν μ T hn ρ δ AΛ Aa dStar dPair Aosc Aelem (spatialRotatePhase R z₀) z') :
    SpatialNekSafeSol ν μ T hn ρ δ AΛ Aa dStar dPair Aosc Aelem z₀
      (fun t => spatialRotatePhase Rᵀ (z' t)) := by
  obtain ⟨h0, hsol, huniq, hst⟩ := h
  have hRR : R * Rᵀ = 1 := mul_transpose_eq_one hR
  have hRt : (Rᵀ)ᵀ * Rᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hRR
  have hback : ∀ w : Phase (n * 3), spatialRotatePhase R (spatialRotatePhase Rᵀ w) = w :=
    fun w => spatialRotatePhase_rotatePhase (R := Rᵀ) (R' := R) hRR w
  have hfwd : ∀ w : Phase (n * 3), spatialRotatePhase Rᵀ (spatialRotatePhase R w) = w :=
    fun w => spatialRotatePhase_rotatePhase (R := R) (R' := Rᵀ) hR w
  refine ⟨by simp [h0, hfwd], isSpatialMovingSolutionOn_rotate hRt hsol, ?_, fun t ht => ?_⟩
  · intro U w hU hconv h0U hw0 hwsol t ht
    have hw' := isSpatialMovingSolutionOn_rotate hR hwsol
    have := huniq U (fun t => spatialRotatePhase R (w t)) hU hconv h0U
      (by simp only [hw0, h0, hback]) hw' t ht
    have h2 := congrArg (spatialRotatePhase Rᵀ) this
    simpa [hfwd] using h2
  · have := hst t ht
    refine SpatialNekSafeState.transport_rotate hR hdet ?_
    simpa [hback] using this

end KAM.Planetary.Spatial

end
