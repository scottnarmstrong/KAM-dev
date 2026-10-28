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
public import KAM.Planetary.PlanarTorsion.Asymptotics.Limits
public import KAM.Planetary.PlanarTorsion.Asymptotics.Normalize

/-!
# Planar quartic torsion: asymptotics of `beta` (P11C, package T19)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, steps `as-in`, `as-pi`, `as-c`, `as-ent`,
`as-det`): `asymptotics` (the three entry limits and the determinant limit `-117/16`, each with
relative error `O(α ^ 2)`, and homogeneity of degree `-2`), `asymptotics_uniform_ratio` (constants
depending on the mass ratio only) and `asymptotics_general_axes` (the determinant limit at general
axes `a`, with `α = a₀ / a₁`).

The entry limits come from `as_ent` (`AsymptoticEntries`), the determinant from `Limits`, the
homogeneity and the normalisation of the physical scales from `Homogeneity` and `Normalize`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter Asymptotics
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler

theorem asymptotics (p : PlanarData) (hp : p.Valid) :
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 0 0) (fun a => 3 * p.m 1 / (4 * p.m0 * p.m 0) * a) ∧
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 0 1) (fun a => -9 / (4 * p.m0) * a ^ (3 / 2 : ℝ)) ∧
    p11c_relativeError (fun a => p11c_beta p ![a, 1] 1 1) (fun a => -3 * p.m 0 / (p.m0 * p.m 1) * a ^ 2) ∧
    p11c_relativeError (fun a => (p11c_beta p ![a, 1]).det) (fun a => -117 / (16 * p.m0 ^ 2) * a ^ 3) ∧
    (∀ a ∈ p11c_axes, ∀ s : ℝ, 0 < s → p11c_beta p (s • a) = (s ^ (-2 : ℤ)) • p11c_beta p a) := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := as_ent p hp
  have hm0 := hp.2.1
  have hm := hp.2.2 0
  have hm1 := hp.2.2 1
  refine ⟨?_, ?_, ?_, ?_, fun a ha s hs => p11cAs_beta_smul p hp a ha hs⟩
  · refine p11cAs_rel (c := 3 * p.m 1 / (4 * p.m0 * p.m 0)) (e := 1) (by positivity)
      (p11cAe_pos.mono fun a _ => by simp) ?_
    exact p11cAe_congr_exp (by norm_num) (h4.congr_left fun a => by simp)
  · refine p11cAs_rel (c := -9 / (4 * p.m0)) (e := 3 / 2)
      (div_ne_zero (by norm_num) (by positivity)) (Eventually.of_forall fun a => rfl) ?_
    exact p11cAe_congr_exp (by norm_num) (h5.congr_left fun a => by ring)
  · refine p11cAs_rel (c := -3 * p.m 0 / (p.m0 * p.m 1)) (e := 2)
      (div_ne_zero (mul_ne_zero (by norm_num) hm.ne') (by positivity))
      (Eventually.of_forall fun a => by simp only [Real.rpow_two, sq]) ?_
    exact p11cAe_congr_exp (by norm_num)
      (h6.congr_left fun a => by simp only [Real.rpow_two]; ring)
  · refine p11cAs_rel (c := -117 / (16 * p.m0 ^ 2)) (e := 3)
      (div_ne_zero (by norm_num) (by positivity)) ?_ ?_
    · exact Eventually.of_forall fun a => by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    · exact p11cAe_congr_exp (by norm_num) ((p11cAs_det p hp).congr_left fun a => by
      rw [show a ^ (3 : ℝ) = a ^ 3 by simp])

end KAM.Planetary

end
