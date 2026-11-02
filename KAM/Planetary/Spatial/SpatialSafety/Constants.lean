/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Orbital
public import KAM.Planetary.Spatial.Geometry
public import KAM.Planetary.StrongAMD.AnalyticDomain
public import KAM.Planetary.StrongAMD.Modulus
public import KAM.Planetary.StrongAMD.PlanarSafety.Constants

/-!
# Elementary estimates of the spatial assembly

Source: (spatial theorem LP2, `LP:MAIN L14 (468–500)`, `T19 (599–603)`), track LP,
non-frozen.

* `spatialKeplerAxis_eq_action_sq`: `a_i = Λ_i²/ν_i²` on the physical carrier.
* `spatial_norm_axis_sub_le`: the action-to-axis estimate (MAIN line 497) for `d = 3`.
* `mem_strongLSet_spatialActionVector`: axes in `A` put the initial actions in `𝓛`.
* The budget lemma `exists_budget_radius` (MAIN (39)) is shared with the planar `PlanarSafety.Constants`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- Physical states satisfy `a_i = Λ_i² / ν_i²`. -/
theorem spatialKeplerAxis_eq_action_sq {ν : Fin n → ℝ} {z : Phase (n * 3)}
    (hz : SpatialNegativeEnergy ν z) (i : Fin n) :
    spatialKeplerAxis ν z i = spatialKeplerAction ν z i ^ 2 / ν i ^ 2 := by
  obtain ⟨-, -, h3, -⟩ := spatial_orbital_identities (z := z) i (hz i)
  have := (hz i).1
  rw [h3]; field_simp

/-- The action-to-axis estimate (MAIN line 497), `d = 3`:
`|a_i - a_i⁰| ≤ |Λ_i - Λ_i⁰| (|Λ_i| + |Λ_i⁰|)/ν_i²`, summed over the (finite) index set. -/
theorem spatial_norm_axis_sub_le {ν : Fin n → ℝ} {C ρ : ℝ} (hC0 : 0 ≤ C)
    {z z' : Phase (n * 3)} (hz : SpatialNegativeEnergy ν z) (hz' : SpatialNegativeEnergy ν z')
    (hC : ∀ i, |spatialKeplerAction ν z i| ≤ C) (hC' : ∀ i, |spatialKeplerAction ν z' i| ≤ C)
    (hρ : ‖(fun i => spatialKeplerAction ν z i) - fun i => spatialKeplerAction ν z' i‖ ≤ ρ) :
    ‖(fun i => spatialKeplerAxis ν z i) - fun i => spatialKeplerAxis ν z' i‖ ≤
      ρ * (2 * C) * ∑ k, 1 / ν k ^ 2 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hS : 0 ≤ ∑ k, 1 / ν k ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hi := (hz i).1
  have h1 : |spatialKeplerAction ν z i - spatialKeplerAction ν z' i| ≤ ρ := by
    have := norm_le_pi_norm ((fun i => spatialKeplerAction ν z i) -
      fun i => spatialKeplerAction ν z' i) i
    simpa using this.trans hρ
  have h2 : |spatialKeplerAction ν z i + spatialKeplerAction ν z' i| ≤ 2 * C :=
    (abs_add_le _ _).trans (by linarith [hC i, hC' i])
  have h3 : spatialKeplerAxis ν z i - spatialKeplerAxis ν z' i =
      (spatialKeplerAction ν z i - spatialKeplerAction ν z' i) *
        (spatialKeplerAction ν z i + spatialKeplerAction ν z' i) / ν i ^ 2 := by
    rw [spatialKeplerAxis_eq_action_sq hz, spatialKeplerAxis_eq_action_sq hz']; ring
  have h4 : 1 / ν i ^ 2 ≤ ∑ k, 1 / ν k ^ 2 :=
    Finset.single_le_sum (f := fun k => 1 / ν k ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ i)
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [h3, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ν i ^ 2), div_eq_mul_one_div]
  calc _ ≤ (ρ * (2 * C)) * (1 / ν i ^ 2) := by
        apply mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hρ0) le_rfl (by positivity)
          (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- Axes in `A` put the initial actions in `𝓛 = strongLSet ν A` (physical states). -/
theorem mem_strongLSet_spatialActionVector {ν : Fin n → ℝ} {A : Set (Fin n → ℝ)}
    {z : Phase (n * 3)} (hA : (fun i => spatialKeplerAxis ν z i) ∈ A) :
    spatialActionVector ν z ∈ strongLSet ν A :=
  ⟨fun i => spatialKeplerAxis ν z i, hA, rfl⟩

end KAM.Planetary.Spatial

end
