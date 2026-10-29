/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries

/-!
# Planar quartic torsion: relative errors (P11C, package T19)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`): `p11c_relativeError f g` says that
`f / g - 1 = O(α ^ 2)` as `α → 0⁺`.  `p11cAs_rel` turns the absolute form
`f = c α ^ e + O(α ^ (e + 2))` of `AsymptoticEntries` into this relative form, and
`p11cAs_rel_explicit` extracts explicit constants from it.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter Asymptotics
open scoped Topology
namespace KAM.Planetary

/-- Relative error O(alpha²); constants depend only on the mass ratio after normalization. -/
def p11c_relativeError (f g : ℝ → ℝ) : Prop :=
  Asymptotics.IsBigO (nhdsWithin 0 (Ioi (0 : ℝ))) (fun a => f a / g a - 1) (fun a => a ^ 2)

/-- From `f - g = O(α ^ (e + 2))` and `g = c α ^ e` (`c ≠ 0`) to the relative error. -/
theorem p11cAs_rel {f g : ℝ → ℝ} {c e : ℝ} (hc : c ≠ 0)
    (hg : ∀ᶠ a : ℝ in 𝓝[>] 0, g a = c * a ^ e)
    (h : (fun a => f a - g a) =O[𝓝[>] 0] fun a : ℝ => a ^ (e + 2)) :
    p11c_relativeError f g := by
  have hinv : (fun a : ℝ => c⁻¹ * a ^ (-e)) =O[𝓝[>] 0] fun a : ℝ => a ^ (-e) :=
    p11cAe_const_mul c⁻¹ (-e)
  have h2 := p11cAe_congr_exp (s := 2) (by ring) (p11cAe_mul h hinv)
  unfold p11c_relativeError
  rw [show (fun a : ℝ => a ^ 2) = fun a : ℝ => a ^ (2 : ℝ) from
    funext fun a => (Real.rpow_two a).symm]
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards [hg, p11cAe_pos] with a ha h0
  have hp : 0 < a ^ e := Real.rpow_pos_of_pos h0 e
  have hne : g a ≠ 0 := by rw [ha]; exact mul_ne_zero hc hp.ne'
  rw [Real.rpow_neg h0.le, ha]
  field_simp

/-- Explicit constants for a relative error. -/
theorem p11cAs_rel_explicit {f g : ℝ → ℝ} (h : p11c_relativeError f g) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ a ∈ Ioo (0 : ℝ) δ, |f a / g a - 1| ≤ C * a ^ 2 := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hc
  refine ⟨max c 1, min δ 1, lt_of_lt_of_le one_pos (le_max_right _ _), lt_min hδ one_pos,
    min_le_right _ _, fun a ha => ?_⟩
  have h1 := hsub ⟨ha.1, lt_of_lt_of_le ha.2 (min_le_left _ _)⟩
  simp only [mem_ofPred_eq, Real.norm_eq_abs] at h1
  rw [abs_of_nonneg (sq_nonneg a)] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg a))

end KAM.Planetary

end
