/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.EntryBounds
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Coeffs
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Projector
public import KAM.Planetary.PlanarTorsion.Beta

/-!
# Planar quartic torsion: the entries of `beta` at hierarchical axes (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-ent`): inserting the sizes of
`as_c` and `as_pi` into `beta_def`, the entries of `p11c_beta p ![α, 1]` satisfy
`β₁₁ = 8 c₁ + O(α ^ (7/2))`, `β₁₂ = 4 c₃ + O(α ^ (7/2))`, `β₂₂ = 8 c₂ + O(α ^ 4)` (blueprint
numbering of the `c`'s), hence the three limits
`β₁₁ = (3 g₀ m₂ / (4 m₁)) α (1 + O(α²))`, `β₁₂ = -(9 g₀ / 4) α ^ (3/2) (1 + O(α²))`,
`β₂₂ = -(3 g₀ m₁ / m₂) α² (1 + O(α²))` with `g₀ = 1 / m₀`, kept in the absolute form
`leading + O(α ^ (leading exponent + 2))`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

/-- `bpP:p11b:asymptotics`, step `as-ent`: the entries of `p11c_beta` at `a = ![α, 1]`. -/
theorem as_ent (p : PlanarData) (hp : p.Valid) :
    (fun α => p11c_beta p ![α, 1] 0 0 - 8 * p11c_coeffs p ![α, 1] 0)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) ∧
      (fun α => p11c_beta p ![α, 1] 0 1 - 4 * p11c_coeffs p ![α, 1] 2)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) ∧
      (fun α => p11c_beta p ![α, 1] 1 1 - 8 * p11c_coeffs p ![α, 1] 1)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => p11c_beta p ![α, 1] 0 0 - 3 * p.m 1 / (4 * p.m0 * p.m 0) * α)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (3 : ℝ)) ∧
      (fun α => p11c_beta p ![α, 1] 0 1 + 9 / (4 * p.m0) * α ^ (3 / 2 : ℝ))
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) ∧
      (fun α => p11c_beta p ![α, 1] 1 1 + 3 * p.m 0 / (p.m0 * p.m 1) * α ^ (2 : ℝ))
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) := by
  obtain ⟨ac0, ac1, ac2, ac3, ac4, ac5⟩ := as_c p hp
  obtain ⟨key, hw, hv⟩ := as_pi p hp
  have hc0 : (fun α => p11c_coeffs p ![α, 1] 0) =O[𝓝[>] 0] fun α : ℝ => α ^ (1 : ℝ) :=
    p11cAe_lead_isBigO (c := 3 * p.m 1 / (32 * p.m0 * p.m 0)) (r := 1) (s := 3) (by norm_num)
      (by simpa using ac0)
  have hc1 : (fun α => p11c_coeffs p ![α, 1] 1) =O[𝓝[>] 0] fun α : ℝ => α ^ (2 : ℝ) :=
    p11cAe_lead_isBigO' (c := 3 * p.m 0 / (8 * p.m0 * p.m 1)) (r := 2) (s := 4) (by norm_num) ac1
  have hc2 : (fun α => p11c_coeffs p ![α, 1] 2) =O[𝓝[>] 0] fun α : ℝ => α ^ (3 / 2 : ℝ) :=
    p11cAe_lead_isBigO' (c := 9 / (16 * p.m0)) (r := 3 / 2) (s := 7 / 2) (by norm_num) ac2
  have e00 : ∀ᶠ α : ℝ in 𝓝[>] 0, p11c_beta p ![α, 1] 0 0 = 8 * (
      p11c_coeffs p ![α, 1] 0 * (1 - p11c_projector p ![α, 1] 1 1) ^ 2 +
      p11c_coeffs p ![α, 1] 1 * p11c_projector p ![α, 1] 1 1 ^ 2 +
      (p11c_coeffs p ![α, 1] 2 + p11c_coeffs p ![α, 1] 3) *
        ((1 - p11c_projector p ![α, 1] 1 1) * p11c_projector p ![α, 1] 1 1) +
      (p11c_coeffs p ![α, 1] 4 * (1 - p11c_projector p ![α, 1] 1 1) +
        p11c_coeffs p ![α, 1] 5 * p11c_projector p ![α, 1] 1 1) *
        p11c_projector p ![α, 1] 0 1) := by
    filter_upwards [key] with a ha
    simp only [p11c_beta, beta_def, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [ha.2.2.2]
    ring
  have e01 : ∀ᶠ α : ℝ in 𝓝[>] 0, p11c_beta p ![α, 1] 0 1 = 4 * (
      4 * (p11c_coeffs p ![α, 1] 0 + p11c_coeffs p ![α, 1] 1) *
        ((1 - p11c_projector p ![α, 1] 1 1) * p11c_projector p ![α, 1] 1 1) +
      p11c_coeffs p ![α, 1] 2 * (1 - 2 * p11c_projector p ![α, 1] 1 1) ^ 2 +
      p11c_coeffs p ![α, 1] 3 * ((1 - 2 * p11c_projector p ![α, 1] 1 1) ^ 2 / 2 -
        2 * ((1 - p11c_projector p ![α, 1] 1 1) * p11c_projector p ![α, 1] 1 1)) +
      2 * (p11c_coeffs p ![α, 1] 5 - p11c_coeffs p ![α, 1] 4) * p11c_projector p ![α, 1] 0 1 *
        (1 - 2 * p11c_projector p ![α, 1] 1 1)) := by
    filter_upwards [key] with a ha
    simp only [p11c_beta, beta_def, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [ha.2.2.2]
    ring
  have e11 : ∀ᶠ α : ℝ in 𝓝[>] 0, p11c_beta p ![α, 1] 1 1 = 8 * (
      p11c_coeffs p ![α, 1] 0 * p11c_projector p ![α, 1] 1 1 ^ 2 +
      p11c_coeffs p ![α, 1] 1 * (1 - p11c_projector p ![α, 1] 1 1) ^ 2 +
      (p11c_coeffs p ![α, 1] 2 + p11c_coeffs p ![α, 1] 3) *
        ((1 - p11c_projector p ![α, 1] 1 1) * p11c_projector p ![α, 1] 1 1) -
      (p11c_coeffs p ![α, 1] 4 * p11c_projector p ![α, 1] 1 1 +
        p11c_coeffs p ![α, 1] 5 * (1 - p11c_projector p ![α, 1] 1 1)) *
        p11c_projector p ![α, 1] 0 1) := by
    filter_upwards [key] with a ha
    simp only [p11c_beta, beta_def, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [ha.2.2.2]
    ring
  have R1 : (fun α => p11c_beta p ![α, 1] 0 0 - 8 * p11c_coeffs p ![α, 1] 0)
      =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) :=
    ((p11cAe_entA hc0 hc1 hc2 ac3 ac4 ac5 hv hw).const_mul_left 8).congr'
      (e00.mono fun a ha => by beta_reduce; rw [ha]; ring) EventuallyEq.rfl
  have R2 : (fun α => p11c_beta p ![α, 1] 0 1 - 4 * p11c_coeffs p ![α, 1] 2)
      =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) :=
    ((p11cAe_entB hc0 hc1 hc2 ac3 ac4 ac5 hv hw).const_mul_left 4).congr'
      (e01.mono fun a ha => by beta_reduce; rw [ha]; ring) EventuallyEq.rfl
  have R3 : (fun α => p11c_beta p ![α, 1] 1 1 - 8 * p11c_coeffs p ![α, 1] 1)
      =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) :=
    ((p11cAe_entE hc0 hc1 hc2 ac3 ac4 ac5 hv hw).const_mul_left 8).congr'
      (e11.mono fun a ha => by beta_reduce; rw [ha]; ring) EventuallyEq.rfl
  refine ⟨R1, R2, R3, ?_, ?_, ?_⟩
  · exact ((R1.trans (p11cAe_rpow_isBigO (by norm_num : (3 : ℝ) ≤ 7 / 2))).add
      (ac0.const_mul_left 8)).congr_left fun a => by ring
  · exact ((R2.trans (p11cAe_rpow_isBigO (by norm_num : (7 / 2 : ℝ) ≤ 7 / 2))).add
      (ac2.const_mul_left 4)).congr_left fun a => by ring
  · exact ((R3.trans (p11cAe_rpow_isBigO (by norm_num : (4 : ℝ) ≤ 4))).add
      (ac1.const_mul_left 8)).congr_left fun a => by ring

end KAM.Planetary

end
