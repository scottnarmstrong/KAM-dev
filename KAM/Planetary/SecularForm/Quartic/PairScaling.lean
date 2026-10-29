/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Defs
public import KAM.Planetary.SecularForm.Basic
public import KAM.Planetary.SecularForm.DiagonalJet.Pair

/-!
# Secular form: scaling of the literal pair average

Blueprint P, Part 8, `stepP:p8:q4-a`: `quartic_pair_scaling`.  The regular orbit map is
`q = (Λ²/(m²κ)) · unitPosition λ v`, so the literal pair average is `-G mᵢ mⱼ / b` times the
dimensionless separated average.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

theorem poincare_fst_eq_unitPosition (m κ : ℝ) {w : Phase 2} (hw : w ∈ poincareDom) :
    (poincare m κ w).1 = (w.2 0 ^ 2 / (m ^ 2 * κ)) • unitPosition (w.1 0) (poincareV w) := by
  obtain ⟨-, hK, -, -, hsq, -, -⟩ := poincare_facts hw
  have hk : √(1 - planeSq (poincareV w)) = poincareK w := by
    rw [hsq]; simp only [sub_sub_cancel]; exact Real.sqrt_sq hK.le
  simp only [poincare, unitPosition, hk, poincareF]

theorem quartic_pair_scaling (D : Data n) {i j : Fin n} (hij : i < j)
    {L1 L2 : ℝ} (hI : 0 < L1) (hJ : 0 < L2) (u v : Fin 2 → ℝ)
    (hu : (![0,u 0],![L1,u 1]) ∈ poincareDom)
    (hv : (![0,v 0],![L2,v 1]) ∈ poincareDom)
    (hSep : (L1^2/(D.m i^2*(D.G*D.m0))/(L2^2/(D.m j^2*(D.G*D.m0))),
      poincareV (![0,u 0],![L1,u 1]), poincareV (![0,v 0],![L2,v 1])) ∈ separatedDomain) :
    pairSlowSecular D i j L1 L2 (u,v) = -D.G*D.m i*D.m j/(L2^2/(D.m j^2*(D.G*D.m0))) *
      dimensionlessPair (L1^2/(D.m i^2*(D.G*D.m0))/(L2^2/(D.m j^2*(D.G*D.m0))),
        poincareV (![0,u 0],![L1,u 1]), poincareV (![0,v 0],![L2,v 1])) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  set a := L1 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) with ha
  set b := L2 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) with hb
  have hb0 : 0 < b := div_pos (pow_pos hJ 2) (mul_pos (pow_pos (D.hm j) 2) hκ)
  have hab : b * (a / b) = a := by field_simp
  unfold pairSlowSecular dimensionlessPair
  have key : ∀ s t : ℝ,
      -D.G * D.m i * D.m j / planeLength
        ((poincare (D.m i) (D.G * D.m0) (![s, u 0], ![L1, u 1])).1 -
          (poincare (D.m j) (D.G * D.m0) (![t, v 0], ![L2, v 1])).1) =
      -D.G * D.m i * D.m j / b *
        (planeLength ((a / b) • unitPosition s (poincareV (![0, u 0], ![L1, u 1])) -
          unitPosition t (poincareV (![0, v 0], ![L2, v 1]))))⁻¹ := by
    intro s t
    have h1 := poincare_fst_eq_unitPosition (D.m i) (D.G * D.m0)
      (mem_poincareDom_congr_fst 0 s _ _ _ hu)
    have h2 := poincare_fst_eq_unitPosition (D.m j) (D.G * D.m0)
      (mem_poincareDom_congr_fst 0 t _ _ _ hv)
    simp only [Matrix.cons_val_zero] at h1 h2
    rw [h1, h2, poincareV_congr_fst s 0, poincareV_congr_fst t 0, ← ha, ← hb]
    have e : a • unitPosition s (poincareV (![0, u 0], ![L1, u 1])) -
        b • unitPosition t (poincareV (![0, v 0], ![L2, v 1])) =
        b • ((a / b) • unitPosition s (poincareV (![0, u 0], ![L1, u 1])) -
          unitPosition t (poincareV (![0, v 0], ![L2, v 1]))) := by
      rw [smul_sub, smul_smul, hab]
    rw [e, planeLength_smul, abs_of_pos hb0]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  simp_rw [key]
  simp_rw [intervalIntegral.integral_const_mul]
  ring

end SecularForm
end KAM.Planetary
end
