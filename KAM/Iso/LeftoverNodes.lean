/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Kepler
public import KAM.Iso.RestrictedHam
public import KAM.Iso.Collision
public import KAM.Iso.Charts.Defs

/-!
# Track I leftover node exports (GAP-ISM)

Literal exports of three nodes left open by the track I sync:

* `k_pos_node` (`stepI:p6:k-pos`): for `κ > 0`, `Ω ≠ 0`, `L > 0`, `3 κ Ω² / L⁴ > 0` and
  `det K_{κ,Ω}(L) > 0`.
* `tori_patch_node` (`stepI:p3:tori-patch`): for a finite family of patches covering `closure B'`,
  `I₀ ∈ closure B'` and `|E - h(I₀)| ≤ ε` with `ε < ε₁ ≤ δ_{E,j}/2`, there is `j` with
  `‖I₀ - c_j‖ < ρ_j`, `|h(I₀) - h(c_j)| < δ_{E,j}/2` and `|E - h(c_j)| ≤ ε + δ_{E,j}/2 ≤ δ_{E,j}`.
* `sec_ham_data` (`bpI:p7:sec-ham#data`): `W_μ` is the collision-free set, equal to the set of
  `(q, p)` with `q ≠ a₁(μ)`, `q ≠ a₂(μ)`; it is open, and `Ham^R3_μ`, `V_μ` are given on it by
  the formulas of the restricted-problem definition (`r_j = radius (q - a_j μ)`).
-/

public section

namespace KAM.Iso

/-- `stepI:p6:k-pos`: `3 κ Ω² / L⁴ > 0`, hence `det K > 0`, for `Ω ≠ 0` (not only `Ω > 0`). -/
theorem k_pos_node {κ Ω : ℝ} (hκ : 0 < κ) (hΩ : Ω ≠ 0) (L : {L : ℝ // 0 < L}) :
    0 < 3 * κ * Ω ^ 2 / L.val ^ 4 ∧ 0 < (keplerBorder κ Ω L).det := by
  have hpos : 0 < 3 * κ * Ω ^ 2 / L.val ^ 4 := by
    have := L.2
    have := pow_pos (abs_pos.2 hΩ) 2
    rw [sq_abs] at this
    positivity
  exact ⟨hpos, by rw [keplerBorder_det]; exact hpos⟩

/-- `bpI:p7:sec-ham#data`: the set `W_μ`, its openness, and the defining formulas of
`Ham^R3_μ` and `V_μ` on it (with `r_j = radius (q - a_j μ)`). -/
theorem sec_ham_data (μ : ℝ) :
    {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | CollisionFree μ z} =
        {z | 0 < radius (z.1 - primary₁ μ) ∧ 0 < radius (z.1 - primary₂ μ)} ∧
      {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | CollisionFree μ z} =
        {z | z.1 ≠ primary₁ μ ∧ z.1 ≠ primary₂ μ} ∧
      IsOpen {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | CollisionFree μ z} ∧
      (∀ (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hz : CollisionFree μ z),
        restrictedHamiltonian μ ⟨z, hz⟩ =
          radiusSq z.2 / 2 + z.1 1 * z.2 0 - z.1 0 * z.2 1 -
            (1 - μ) / radius (z.1 - primary₁ μ) - μ / radius (z.1 - primary₂ μ)) ∧
      (∀ (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hz : CollisionFree μ z),
        restrictedVectorField μ ⟨z, hz⟩ =
          (![z.2 0 + z.1 1, z.2 1 - z.1 0],
            ![z.2 1, -z.2 0] -
              ((1 - μ) / radius (z.1 - primary₁ μ) ^ 3) • (z.1 - primary₁ μ) -
              (μ / radius (z.1 - primary₂ μ) ^ 3) • (z.1 - primary₂ μ))) := by
  refine ⟨rfl, ?_, isOpen_collisionFree μ, fun _ _ => rfl, fun _ _ => rfl⟩
  ext z
  have key : ∀ a : Fin 2 → ℝ, 0 < radius (z.1 - a) ↔ z.1 ≠ a := fun a => by
    rw [(Collision.radius_nonneg _).lt_iff_ne, Ne, eq_comm, Collision.radius_eq_zero_iff,
      sub_eq_zero]
  exact and_congr (key _) (key _)

end KAM.Iso

namespace KAM.Iso.Charts

open Set Metric KAM.Iso.Confinement

/-- `stepI:p3:tori-patch`: the patches `(c, W_c, Ψ_c, δ_E, δ_m, ρ_c)` (`bpI:p3:patch`) of a finite
cover of `closure B'` (`bpI:p3:cover`) are fixed with `ε₁ ≤ δ_{E,c} / 2` (`bpI:p3:uniform`)
before `ε, E, I₀`; for `0 ≤ ε < ε₁`, `I₀ ∈ closure B'` and `|E - h(I₀)| ≤ ε` there is a patch
centre `c` with `‖I₀ - c‖ < ρ_c`, `|h(I₀) - h(c)| < δ_E/2`, and
`|E - h(c)| ≤ ε + δ_E/2 ≤ δ_E`. -/
theorem tori_patch_node {h : (Fin 2 → ℂ) → ℂ} {B : Set (Fin 2 → ℝ)} {r₀ : ℝ}
    {B' : Set (Fin 2 → ℝ)} {η₁ : ℝ} (P : Finset (Fin 2 → ℝ))
    (W : (Fin 2 → ℝ) → Set (Fin 2 → ℝ)) (Ψ : (Fin 2 → ℝ) → ℝ × ℝ → Fin 2 → ℝ)
    (δE δm ρc : (Fin 2 → ℝ) → ℝ)
    (hP : ∀ c ∈ P, IsPatch h B r₀ B' η₁ c (W c) (Ψ c) (δE c) (δm c) (ρc c))
    (hcov : closure B' ⊆ ⋃ c ∈ P, ball c (ρc c)) {ε₁ : ℝ} (hε₁ : ∀ c ∈ P, ε₁ ≤ δE c / 2)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < ε₁) {I₀ : Fin 2 → ℝ} (hI₀ : I₀ ∈ closure B') {E : ℝ}
    (hE : |E - realPart h I₀| ≤ ε) :
    ∃ c ∈ P, ‖I₀ - c‖ < ρc c ∧ |realPart h I₀ - realPart h c| < δE c / 2 ∧
      |E - realPart h c| ≤ ε + δE c / 2 ∧ ε + δE c / 2 ≤ δE c := by
  obtain ⟨c, hcP, hcb⟩ := Set.mem_iUnion₂.1 (hcov hI₀)
  have h1 := (hP c hcP).ball_h I₀ hcb
  have h2 : ε < δE c / 2 := hε.trans_le (hε₁ c hcP)
  refine ⟨c, hcP, mem_ball_iff_norm.1 hcb, h1, ?_, by linarith⟩
  calc |E - realPart h c| ≤ |E - realPart h I₀| + |realPart h I₀ - realPart h c| :=
        abs_sub_le _ _ _
    _ ≤ ε + δE c / 2 := by linarith

end KAM.Iso.Charts
