/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Newtonian.AssemblyNodes

/-!
# Graph-node export: the Newton projection of the tube assembly (GAP-PX)

Unsigned export stating the literal conclusion of `stepP:p6:ma-newton` from its source
hypotheses (S1), (S2), built from the landed `ma_coll` and `orbit_transfer_moving`.
-/

public section

namespace KAM.Planetary

open KAM KAM.Kepler

variable {n : ℕ}

/-- `stepP:p6:ma-newton`: every point of `S` lies on a physical torus inside `S` whose orbits
(through `K φ`) are Newton solutions for the actual masses. -/
theorem ma_newton {G m0 μ : ℝ} {m a : Fin n → ℝ} {γ A η : ℝ} (h : AxisData a γ A)
    (hη : 0 < η) (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ)
    {S : Set (Phase (n * 2))} (_hS : MeasurableSet S)
    (hSt : S ⊆ circularTube G m0 m a (tubeRadius η γ))
    (hS2 : ∀ z ∈ S, ∃ (w : Fin (n * 2) → ℝ) (K : (Fin (n * 2) → ℝ) → Phase (n * 2))
      (θ : Fin (n * 2) → ℝ), K θ = z ∧ Set.range K ⊆ S ∧
        IsPhysicalTorus (movingHamiltonian G m0 m μ) w K) :
    ∀ z ∈ S, ∃ (w : Fin (n * 2) → ℝ) (K : (Fin (n * 2) → ℝ) → Phase (n * 2))
      (θ : Fin (n * 2) → ℝ), K θ = z ∧ Set.range K ⊆ S ∧
        IsPhysicalTorus (movingHamiltonian G m0 m μ) w K ∧
        ∀ φ, IsNewtonSolution G (actualMasses m0 m μ)
          (fun t => barycentricPositions m0 m μ (K (φ + t • w)).1)
          (fun t => barycentricVelocities m0 m μ (K (φ + t • w)).2) := by
  intro z hz
  obtain ⟨w, K, θ, hKz, hKS, hK⟩ := hS2 z hz
  exact ⟨w, K, θ, hKz, hKS, hK, fun φ =>
    orbit_transfer_moving hG hm0 hm hμ hK (ma_coll h hη hSt hKS) φ⟩

end KAM.Planetary
