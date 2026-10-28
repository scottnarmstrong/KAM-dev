/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries
public import KAM.Planetary.PlanarTorsion.Asymptotics.Homogeneity
public import KAM.Planetary.PlanarTorsion.Asymptotics.Relative

/-!
# Planar quartic torsion: the limits of `beta` (P11C, package T19)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-det`): the three entry limits
with relative error `O(α ^ 2)` (from `as_ent`), the determinant limit `-117/16` (the leading
parts of `β₁₁ β₂₂ - β₁₂ ^ 2` combine to `(-9/4 - 81/16) / m₀ ^ 2`), and homogeneity of degree `-2`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter Asymptotics
open scoped Topology
namespace KAM.Planetary

/-- `as-det`: the determinant is `-117/(16 m₀²) α³` up to `O(α ^ 5)`. -/
theorem p11cAs_det (p : PlanarData) (hp : p.Valid) :
    (fun α => (p11c_beta p ![α, 1]).det - (-117 / (16 * p.m0 ^ 2) * α ^ (3 : ℝ)))
      =O[𝓝[>] 0] fun α : ℝ => α ^ (5 : ℝ) := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := as_ent p hp
  have hm0 := hp.2.1
  have hm := hp.2.2 0
  have hm1 := hp.2.2 1
  have hd : (fun α => p11c_beta p ![α, 1] 1 1) =O[𝓝[>] 0] fun α : ℝ => α ^ (2 : ℝ) :=
    p11cAe_lead_isBigO' (c := 3 * p.m 0 / (p.m0 * p.m 1)) (by norm_num) h6
  have hb : (fun α => p11c_beta p ![α, 1] 0 1) =O[𝓝[>] 0] fun α : ℝ => α ^ (3 / 2 : ℝ) :=
    p11cAe_lead_isBigO' (c := 9 / (4 * p.m0)) (r := 3 / 2) (by norm_num) h5
  have hb' : (fun α => p11c_beta p ![α, 1] 0 1 - 9 / (4 * p.m0) * α ^ (3 / 2 : ℝ))
      =O[𝓝[>] 0] fun α : ℝ => α ^ (3 / 2 : ℝ) :=
    hb.sub (p11cAe_const_mul _ _)
  have hA : (fun α => 3 * p.m 1 / (4 * p.m0 * p.m 0) * α) =O[𝓝[>] 0] fun α : ℝ => α ^ (1 : ℝ) :=
    ((p11cAe_const_mul (3 * p.m 1 / (4 * p.m0 * p.m 0)) 1).congr_left fun a => by
      rw [Real.rpow_one])
  have t1 := p11cAe_congr_exp (s := 5) (by norm_num) (p11cAe_mul h4 hd)
  have t2 := p11cAe_congr_exp (s := 5) (by norm_num) (p11cAe_mul hA h6)
  have t3 := p11cAe_congr_exp (s := 5) (by norm_num) (p11cAe_mul h5 hb')
  have key := (t1.add t2).sub t3
  refine key.congr' ?_ EventuallyEq.rfl
  filter_upwards [p11cAe_pos] with a ha
  have hs : p11c_beta p ![a, 1] 1 0 = p11c_beta p ![a, 1] 0 1 := by
    simp only [p11c_beta, beta_def, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have h2 : a ^ (2 : ℝ) = a * a := by rw [Real.rpow_two, sq]
  have h3 : a ^ (3 : ℝ) = a * a * a := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have h32 : a ^ (3 / 2 : ℝ) * a ^ (3 / 2 : ℝ) = a * a * a := by
    rw [← Real.rpow_add ha, ← h3]; norm_num
  rw [Matrix.det_fin_two, hs]
  simp only [h3, h2]
  have hm0' := hm0.ne'
  have hm' := hm.ne'
  have hm1' := hm1.ne'
  field_simp
  linear_combination (1296 * p.m 0 : ℝ) * h32

end KAM.Planetary

end
