/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Rotation
public import KAM.Planetary.Spatial.RotationSolution
public import KAM.Planetary.Spatial.Alignment
public import KAM.Planetary.Spatial.Osculating.Basic
public import KAM.Planetary.Spatial.Newton
public import KAM.Planetary.StrongAMD.Threshold

/-!
# Rotation alignment of the spatial safety conclusion

Package LP-SP-SAFE (spatial theorem LP2, MAIN Theorem 19 with Lemma 16 and Lemma 18, `d = 3`;
`LP:MAIN T19 (599–603)`, `L18 (595–597)`), track LP, non-frozen.

`SpatialSafeState` is the per-time conjunction of the conclusions of the spatial safety theorem
(ellipticity, AMD margin, drifts, separations, osculating clauses) and `SpatialSafeSol` the
solution-level conclusion without the Newtonian reconstruction.  The spatial analogue of the
planar reflection is the rotation `spatialRotatePhase R` (LP-SP-MODEL): every conclusion quantity
is rotation invariant, and
`SpatialSafeSol … (spatialRotatePhase R z₀) z' →
  SpatialSafeSol … z₀ (spatialRotatePhase Rᵀ ∘ z')`.
Only invariances are proved here: the osculating velocity, elements and ellipse data, and the
moving uniqueness predicate.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Matrix

variable {n : ℕ} {R : Matrix (Fin 3) (Fin 3) ℝ}

section Invariance

variable (hR : Rᵀ * R = 1)
include hR

theorem spaceLength_bodyVector3_rotate (z : Phase (n * 3)) (i : Fin n) :
    spaceLength (bodyVector3 (spatialRotatePhase R z).1 i) = spaceLength (bodyVector3 z.1 i) := by
  simp only [spatialRotatePhase, bodyVector3_rotateBlocks, spaceLength_mulVec hR]

theorem spaceLength_bodyVector3_rotate_sub (z : Phase (n * 3)) (i j : Fin n) :
    spaceLength (bodyVector3 (spatialRotatePhase R z).1 i -
      bodyVector3 (spatialRotatePhase R z).1 j) =
      spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j) := by
  simp only [spatialRotatePhase, bodyVector3_rotateBlocks, ← Matrix.mulVec_sub,
    spaceLength_mulVec hR]

omit hR in
theorem spatialOscVelocity_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscVelocity ν μ (spatialRotatePhase R z) i = R *ᵥ spatialOscVelocity ν μ z i := by
  have hsum : ∑ j, R *ᵥ bodyVector3 z.2 j = R *ᵥ ∑ j, bodyVector3 z.2 j :=
    (Matrix.mulVec_sum _ _ _).symm
  unfold spatialOscVelocity
  simp only [spatialRotatePhase, bodyVector3_rotateBlocks, hsum, Matrix.mulVec_add,
    Matrix.mulVec_smul]

theorem spatialOscEnergy_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscEnergy ν μ (spatialRotatePhase R z) i = spatialOscEnergy ν μ z i := by
  unfold spatialOscEnergy
  rw [spatialOscVelocity_rotate, spaceSq_mulVec hR, spaceLength_bodyVector3_rotate hR]

theorem spatialOscAxis_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscAxis ν μ (spatialRotatePhase R z) i = spatialOscAxis ν μ z i := by
  unfold spatialOscAxis
  rw [spatialOscEnergy_rotate hR]

theorem spatialOscEccVector_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscEccVector ν μ (spatialRotatePhase R z) i = R *ᵥ spatialOscEccVector ν μ z i := by
  unfold spatialOscEccVector
  simp only [spatialOscVelocity_rotate]
  simp only [spatialRotatePhase, bodyVector3_rotateBlocks, spaceSq_mulVec hR,
    spaceLength_mulVec hR, spaceDot_mulVec hR, Matrix.mulVec_smul,
    Matrix.mulVec_sub]

theorem spatialOscEcc_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscEcc ν μ (spatialRotatePhase R z) i = spatialOscEcc ν μ z i := by
  unfold spatialOscEcc
  rw [spatialOscEccVector_rotate hR, spaceLength_mulVec hR]

theorem spatialOscPeri_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscPeri ν μ (spatialRotatePhase R z) i = spatialOscPeri ν μ z i := by
  unfold spatialOscPeri
  rw [spatialOscAxis_rotate hR, spatialOscEcc_rotate hR]

theorem spatialOscApo_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscApo ν μ (spatialRotatePhase R z) i = spatialOscApo ν μ z i := by
  unfold spatialOscApo
  rw [spatialOscAxis_rotate hR, spatialOscEcc_rotate hR]

theorem spatialKeplerPeri_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerPeri ν (spatialRotatePhase R z) i = spatialKeplerPeri ν z i := by
  unfold spatialKeplerPeri
  rw [spatialKeplerAxis_rotate hR, spaceLength_spatialKeplerEccVector_rotate hR]

theorem spatialKeplerApo_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialKeplerApo ν (spatialRotatePhase R z) i = spatialKeplerApo ν z i := by
  unfold spatialKeplerApo
  rw [spatialKeplerAxis_rotate hR, spaceLength_spatialKeplerEccVector_rotate hR]

/-- The osculating-minus-canonical eccentricity vector rotates with `R`, so its length is
invariant. -/
theorem spaceLength_oscEccVector_sub_rotate (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3))
    (i : Fin n) :
    spaceLength (spatialOscEccVector ν μ (spatialRotatePhase R z) i -
      spatialKeplerEccVector ν (spatialRotatePhase R z) i) =
      spaceLength (spatialOscEccVector ν μ z i - spatialKeplerEccVector ν z i) := by
  rw [spatialOscEccVector_rotate hR, spatialKeplerEccVector_rotate hR, ← Matrix.mulVec_sub,
    spaceLength_mulVec hR]

theorem spatialActionVector_rotate (ν : Fin n → ℝ) (z : Phase (n * 3)) :
    (fun i => spatialKeplerAction ν (spatialRotatePhase R z) i) =
      fun i => spatialKeplerAction ν z i :=
  funext fun i => spatialKeplerAction_rotate hR ν z i

end Invariance

/-- The per-time conclusions of the spatial safety theorem at a state `zt`, relative to the
initial state `z₀` (`LP:MAIN T19 (599–603)`, `L16`; the clauses of LP1 in the order written
there, with `d = 3`). -/
def SpatialSafeState (ν : Fin n → ℝ) (μ : ℝ) (hn : 2 ≤ n)
    (δ AΛ Aa dStar dPair Aosc Aelem : ℝ) (z₀ zt : Phase (n * 3)) : Prop :=
  (∀ i, 0 < spaceLength (bodyVector3 zt.1 i) ∧ spatialKeplerEnergy ν zt i < 0) ∧
  (∃ hcht : (fun i => spatialKeplerAction ν zt i) ∈ chamber ν,
    spatialStrongAMD ν zt ≤ orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
  ‖(fun i => spatialKeplerAction ν zt i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
    AΛ * Real.sqrt μ ∧
  ‖(fun i => spatialKeplerAxis ν zt i) - fun i => spatialKeplerAxis ν z₀ i‖ ≤
    Aa * Real.sqrt μ ∧
  |spatialStrongAMD ν zt - spatialStrongAMD ν z₀| ≤ n * AΛ * Real.sqrt μ ∧
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
def SpatialSafeSol (ν : Fin n → ℝ) (μ T : ℝ) (hn : 2 ≤ n)
    (δ AΛ Aa dStar dPair Aosc Aelem : ℝ) (z₀ : Phase (n * 3)) (z : ℝ → Phase (n * 3)) : Prop :=
  z 0 = z₀ ∧ IsSpatialMovingSolutionOn ν μ (Icc (-T) T) z ∧
    SpatialMovingUniqueOn ν μ (Icc (-T) T) z ∧
    ∀ t ∈ Icc (-T) T, SpatialSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem z₀ (z t)

/-- Rotation transports the per-time conclusion back: if the state `R zt` satisfies the
conclusions relative to `R z₀`, then `zt` satisfies them relative to `z₀`. -/
theorem SpatialSafeState.of_rotate (hR : Rᵀ * R = 1) (hdet : R.det = 1) {ν : Fin n → ℝ} {μ : ℝ}
    {hn : 2 ≤ n} {δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ zt : Phase (n * 3)}
    (h : SpatialSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem (spatialRotatePhase R z₀)
      (spatialRotatePhase R zt)) :
    SpatialSafeState ν μ hn δ AΛ Aa dStar dPair Aosc Aelem z₀ zt := by
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
theorem SpatialSafeSol.of_rotate (hR : Rᵀ * R = 1) (hdet : R.det = 1) {ν : Fin n → ℝ} {μ T : ℝ}
    {hn : 2 ≤ n} {δ AΛ Aa dStar dPair Aosc Aelem : ℝ} {z₀ : Phase (n * 3)}
    {z' : ℝ → Phase (n * 3)}
    (h : SpatialSafeSol ν μ T hn δ AΛ Aa dStar dPair Aosc Aelem (spatialRotatePhase R z₀) z') :
    SpatialSafeSol ν μ T hn δ AΛ Aa dStar dPair Aosc Aelem z₀
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
    refine SpatialSafeState.of_rotate hR hdet ?_
    simpa [hback] using this

end KAM.Planetary.Spatial

end
