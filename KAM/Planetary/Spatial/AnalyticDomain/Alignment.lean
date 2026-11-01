/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Safety
public import KAM.Planetary.Spatial.Alignment
public import KAM.Planetary.Spatial.RotationSolution

/-!
# The alignment remark of Lemma 18

Package LP-SP-DOM, `LP:MAIN L18 (595–597)`, track LP, non-frozen. The statement surface is
proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For a spatial moving solution with `L ≠ 0`, one fixed rotation `R` takes `L/|L|` to `e₃`
(`exists_rotation_align_angularMomentum3`, SP-MODEL). Along the rotated solution `L` is conserved,
so it stays aligned, and `C = Σ Λ_i − |L|` equals the fixed-plane deficit `C_{e₃}`:

* `spatialStrongAMD_eq_spatialFixedPlaneDeficit_of_aligned`: aligned states have `C = C_{e₃}`;
* `spatialStrongAMD_eq_spatialSlowDeficit_of_aligned`: for chart points `C = (Σ slow²)/2`
  (SP-PROD `spatialStrongAMD_spatialPoincareProd_of_aligned`);
* `aligned_rotated_solution_stays_aligned`: conservation of `L` keeps an aligned rotated solution
  aligned on an order-connected interval;
* `exists_aligned_rotated_solution`: the packaged statement for an actual solution with `L ≠ 0`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary Matrix

variable {n : ℕ} {ν : Fin n → ℝ}

theorem spaceE3_eq_e₃ : spaceE3 = e₃ := rfl

/-- A state with `L = |L| e₃` has `C = C_{e₃}`. -/
theorem spatialStrongAMD_eq_spatialFixedPlaneDeficit_of_aligned (ν : Fin n → ℝ)
    {z : Phase (n * 3)} (hL : angularMomentum3 z = spaceLength (angularMomentum3 z) • e₃) :
    spatialStrongAMD ν z = spatialFixedPlaneDeficit ν z := by
  unfold spatialStrongAMD spatialFixedPlaneDeficit
  have : angularMomentum3 z ⬝ᵥ e₃ = spaceLength (angularMomentum3 z) := by
    conv_lhs => rw [hL]
    rw [smul_dotProduct]
    simp [e₃, dotProduct, Fin.sum_univ_three]
  rw [this]

/-- A nonzero `L` with `L/|L| = e₃` satisfies `L = |L| e₃`. -/
theorem eq_smul_e₃_of_spatialUnit_eq {L : Fin 3 → ℝ} (hL : L ≠ 0) (hu : spatialUnit L = spaceE3) :
    L = spaceLength L • e₃ := by
  have h := spaceLength_pos_iff.mpr hL
  calc L = spaceLength L • spatialUnit L := by
        unfold spatialUnit
        rw [smul_inv_smul₀ h.ne']
    _ = spaceLength L • e₃ := by rw [hu]; rfl

/-- For chart points whose image has `L = |L| e₃`: `C = (Σ slow²)/2 = Σ (Γ_i + Z_i)`
(`LP:MAIN L18 (595)`). -/
theorem spatialStrongAMD_eq_spatialSlowDeficit_of_aligned (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n)
    (hL : angularMomentum3 (spatialPoincareProd ν w) =
      spaceLength (angularMomentum3 (spatialPoincareProd ν w)) • e₃) :
    spatialStrongAMD ν (spatialPoincareProd ν w) =
      ((∑ k, slow w.1 k ^ 2) + ∑ k, slow w.2 k ^ 2) / 2 := by
  rw [spatialStrongAMD_spatialPoincareProd_of_aligned hν hw hL,
    sum_gamma_add_z_eq_half_slow_sq]

/-- Conservation of `L` keeps an aligned rotated solution aligned (`LP:MAIN L18 (597)`): if
`L (R z t₀) = |L (R z t₀)| e₃` at one time of an order-connected set `J`, then at every time. -/
theorem aligned_rotated_solution_stays_aligned {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1)
    {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected) {z : ℝ → Phase (n * 3)}
    (hz : IsSpatialMovingSolutionOn ν μ J z) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h0 : angularMomentum3 (spatialRotatePhase R (z t₀)) =
      spaceLength (angularMomentum3 (spatialRotatePhase R (z t₀))) • e₃) :
    ∀ t ∈ J, angularMomentum3 (spatialRotatePhase R (z t)) =
      spaceLength (angularMomentum3 (spatialRotatePhase R (z t))) • e₃ := by
  intro t ht
  have hc := angularMomentum3_const hJ (isSpatialMovingSolutionOn_rotate hR hz) t₀ ht₀ t ht
  rw [hc]
  exact h0

/-- The packaged alignment statement (`LP:MAIN L18 (595–597)`): for a spatial moving solution with
`L ≠ 0` at some time `t₀ ∈ J`, there is one fixed rotation `R` such that the rotated solution is a
solution, `L` stays `|L| e₃` along it, and `C = C_{e₃}` along it, with `C` the same as for the
original solution. -/
theorem exists_aligned_rotated_solution {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    {z : ℝ → Phase (n * 3)} (hz : IsSpatialMovingSolutionOn ν μ J z) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hL : angularMomentum3 (z t₀) ≠ 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, Rᵀ * R = 1 ∧ R.det = 1 ∧
      IsSpatialMovingSolutionOn ν μ J (fun t => spatialRotatePhase R (z t)) ∧
      ∀ t ∈ J,
        angularMomentum3 (spatialRotatePhase R (z t)) =
            spaceLength (angularMomentum3 (spatialRotatePhase R (z t))) • e₃ ∧
        spatialStrongAMD ν (spatialRotatePhase R (z t)) =
            spatialFixedPlaneDeficit ν (spatialRotatePhase R (z t)) ∧
        spatialStrongAMD ν (spatialRotatePhase R (z t)) = spatialStrongAMD ν (z t) := by
  obtain ⟨R, hR, hdet, hu⟩ := exists_rotation_align_angularMomentum3 hL
  have hne : angularMomentum3 (spatialRotatePhase R (z t₀)) ≠ 0 := by
    rw [angularMomentum3_rotate hR hdet]
    rw [← spaceLength_pos_iff, spaceLength_mulVec hR, spaceLength_pos_iff]
    exact hL
  have h0 := eq_smul_e₃_of_spatialUnit_eq hne hu
  have hal := aligned_rotated_solution_stays_aligned hR hJ hz ht₀ h0
  exact ⟨R, hR, hdet, isSpatialMovingSolutionOn_rotate hR hz, fun t ht =>
    ⟨hal t ht, spatialStrongAMD_eq_spatialFixedPlaneDeficit_of_aligned ν (hal t ht),
      spatialStrongAMD_rotate hR hdet ν (z t)⟩⟩

end KAM.Planetary.Spatial

end
