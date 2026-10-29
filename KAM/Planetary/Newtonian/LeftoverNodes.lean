/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Planetary.Newtonian.Models
public import KAM.Planetary.Newtonian.Reconstruction

/-!
# Bundle exports for Part 6 step nodes

One-line exports of `stepP:p6:pl-a`, `pl-b`, `pl-c`, `dom-smooth`, `rc-pack` and `ot-apply`,
each assembled from landed declarations of `KAM.Kepler.Plane`, `KAM.Planetary.Newtonian.Models`
and `KAM.Planetary.Newtonian.Reconstruction`.
-/

public section

open Set Real Function
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

/-- `stepP:p6:pl-a`: algebraic properties of the planar length, with the triangle inequality. -/
theorem planeLength_algebra (v w : Fin 2 → ℝ) (c : ℝ) :
    0 ≤ planeLength v ∧ planeLength v ^ 2 = planeSq v ∧ planeSq v = planeDot v v ∧
    (planeLength v = 0 ↔ v = 0) ∧ planeLength (-v) = planeLength v ∧
    planeLength (c • v) = |c| * planeLength v ∧
    planeLength (v + w) ≤ planeLength v + planeLength w :=
  ⟨planeLength_nonneg v, planeLength_sq v, planeSq_eq_planeDot v, planeLength_eq_zero_iff,
    planeLength_neg v, planeLength_smul c v, planeLength_add_le v w⟩

/-- `stepP:p6:pl-b`: comparison of the planar length with the max norm. -/
theorem planeLength_norm_bounds (v : Fin 2 → ℝ) :
    ‖v‖ ≤ planeLength v ∧ planeLength v ≤ Real.sqrt 2 * ‖v‖ :=
  ⟨norm_le_planeLength v, planeLength_le_sqrt_two_mul_norm v⟩

/-- `stepP:p6:pl-c`: smoothness of `l` and `1/l` away from `0`, and their derivatives. -/
theorem planeLength_smooth_deriv (v : Fin 2 → ℝ) (hv : v ≠ 0) (h : Fin 2 → ℝ) :
    ContDiffAt ℝ ∞ planeLength v ∧ ContDiffAt ℝ ∞ (fun x => (planeLength x)⁻¹) v ∧
    fderiv ℝ planeLength v h = planeDot v h / planeLength v ∧
    fderiv ℝ (fun x => (planeLength x)⁻¹) v h = -(planeDot v h) / planeLength v ^ 3 := by
  refine ⟨(analyticAt_planeLength hv).contDiffAt.of_le le_top,
    (analyticAt_inv_planeLength hv).contDiffAt.of_le le_top, ?_, ?_⟩
  · rw [(hasFDerivAt_planeLength hv).fderiv]
    simp [planeDot, div_eq_inv_mul]
    ring
  · rw [(hasFDerivAt_inv_planeLength hv).fderiv]
    simp [planeDot, div_eq_inv_mul]
    ring

/-- `stepP:p6:dom-smooth`: both Hamiltonians are `C^∞` on the collision-free set. -/
theorem hamiltonians_contDiffOn {n : ℕ} (G m0 : ℝ) (m : Fin n → ℝ) (μ ε : ℝ) :
    ContDiffOn ℝ ∞ (movingHamiltonian G m0 m μ) (collisionFreeDomain n) ∧
    ContDiffOn ℝ ∞ (fixedHamiltonian G m0 m ε) (collisionFreeDomain n) :=
  ⟨(analyticOnNhd_movingHamiltonian G m0 m μ).contDiffOn
      (isOpen_collisionFreeDomain n).uniqueDiffOn |>.of_le le_top,
    (analyticOnNhd_fixedHamiltonian G m0 m ε).contDiffOn
      (isOpen_collisionFreeDomain n).uniqueDiffOn |>.of_le le_top⟩

/-- `stepP:p6:rc-pack`: reconstruction of Newton solutions on `J`, and for all time. -/
theorem reconstruction_pack {n : ℕ} {G m0 μ : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) (J : Set ℝ) (z : ℝ → Phase (n * 2))
    (hz : ∀ t ∈ J, NoCollision (z t).1 ∧
      HasDerivAt z (hamiltonianVectorField (movingHamiltonian G m0 m μ) (z t)) t) :
    IsNewtonSolutionOn (fun k => G * actualMasses m0 m μ k) J
      (fun t => barycentricPositions m0 m μ (z t).1)
      (fun t => barycentricVelocities m0 m μ (z t).2) ∧
    (J = Set.univ → IsNewtonSolution G (actualMasses m0 m μ)
      (fun t => barycentricPositions m0 m μ (z t).1)
      (fun t => barycentricVelocities m0 m μ (z t).2)) :=
  ⟨reconstruction hG hm0 hm hμ hz, fun hJ =>
    reconstruction_all_time hG hm0 hm hμ fun t => hz t (hJ ▸ mem_univ t)⟩

/-- `stepP:p6:ot-apply`: orbits of a physical torus solve Newton's (resp. the fixed-centre)
equations. -/
theorem orbit_transfer_pack {n : ℕ} {G m0 μ ε : ℝ} {m : Fin n → ℝ} (hG : 0 < G) (hm0 : 0 < m0)
    (hm : ∀ i, 0 < m i) (hμ : 0 ≤ μ) (w : Fin (n * 2) → ℝ)
    (K : (Fin (n * 2) → ℝ) → Phase (n * 2)) :
    (IsPhysicalTorus (movingHamiltonian G m0 m μ) w K → (∀ φ, NoCollision (K φ).1) →
      ∀ φ, IsNewtonSolution G (actualMasses m0 m μ)
        (fun t => barycentricPositions m0 m μ (K (φ + t • w)).1)
        (fun t => barycentricVelocities m0 m μ (K (φ + t • w)).2)) ∧
    (IsPhysicalTorus (fixedHamiltonian G m0 m ε) w K → (∀ φ, NoCollision (K φ).1) →
      ∀ φ, IsFixedSolution G m0 m ε (fun t i => bodyVector (K (φ + t • w)).1 i)
        (fun t i => (1 / m i) • bodyVector (K (φ + t • w)).2 i)) :=
  ⟨fun hK hnc φ => orbit_transfer_moving hG hm0 hm hμ hK hnc φ,
    fun hK hnc φ => orbit_transfer_fixed hm0 hm hK hnc φ⟩

end KAM.Planetary
