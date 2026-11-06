/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.Hw
public import KAM.EffectiveStability.Tube.Chart.Rotation

/-!
# `SJSU18-O2` in modal variables (T2-CONF, N5a)

With `V′ = M / N` (`sjsuV`) and `w_k = (y.2 k - i y.1 k)/√2`:
`sjsu18O2 (rotMap V′ y) = Re (10^{-E} Σ_{d < 10} H_{w,d}(w / N, w̄ / N))` (`sjsu18O2_rotMap`), where
`H_{w,d}` is the literal integer polynomial `sjsuHw d`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Complex

/-- `z_j = (ξ_j - i η_j)/√2` of a phase point `x = (η, ξ)`. -/
def zOf (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℂ :=
  fun j => ((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ)

/-- The model as a sum of summands. The proof compares the summands pointwise
(`List.map_congr_left`): a definitional check of the whole sums would make the kernel evaluate the
7,941-term list. -/
theorem sjsu18O2_eq_sum (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    sjsu18O2 x = ((sjsu18O2Terms.map (sjsuSummand (zOf x))).sum).re := by
  unfold sjsu18O2
  refine congrArg Complex.re (congrArg List.sum (List.map_congr_left fun t _ => ?_))
  rfl

/-- **The model as an integer polynomial, by degree.** -/
theorem sjsu18O2_eq_intChunks (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    sjsu18O2 x = (((10 : ℂ) ^ sjsuE)⁻¹ * ∑ d ∈ Finset.range 10,
      bevalAt (sjsuIntChunks d).flatten (zOf x) (fun k => star (zOf x k))).re := by
  have hok := List.all_eq_true.1 sjsuTerms_ok
  rw [sjsu18O2_eq_sum, sum_sjsuSummand _ _ (fun t ht => by
      have := hok t ht; simp only [Bool.and_eq_true, beq_iff_eq] at this; exact this.1),
    bevalAt_eq_sum_filter_deg _ _ _ (fun e he => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
      have := hok t ht; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2)]
  simp only [flatten_sjsuIntChunks]

/-- The scaled modal variable `w_k / N`, `w_k = (y.2 k - i y.1 k)/√2`. -/
def omegaOf (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℂ :=
  fun k => ((sjsuN : ℂ))⁻¹ * (((y.2 k : ℂ) - Complex.I * (y.1 k : ℂ)) / (Real.sqrt 2 : ℂ))

theorem zOf_rotMap (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    zOf (rotMap sjsuV y) = sjsuM.apply (omegaOf y) := by
  have hN : (sjsuN : ℂ) ≠ 0 := by norm_num [sjsuN]
  funext j
  simp only [zOf, rotMap, Mat3.apply_eq, omegaOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    sjsuV]
  push_cast
  field_simp
  ring

theorem star_zOf_rotMap (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    (fun k => star (zOf (rotMap sjsuV y) k)) = sjsuM.apply (fun k => star (omegaOf y k)) := by
  rw [zOf_rotMap]
  funext j
  simp only [Mat3.apply_eq, star_add, star_mul', Complex.star_def, map_intCast]

/-- **`SJSU18-O2` in modal variables.** -/
theorem sjsu18O2_rotMap (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    sjsu18O2 (rotMap sjsuV y) = (((10 : ℂ) ^ sjsuE)⁻¹ * ∑ d ∈ Finset.range 10,
      bevalAt (sjsuHw d) (omegaOf y) (fun k => star (omegaOf y k))).re := by
  rw [sjsu18O2_eq_intChunks, star_zOf_rotMap, zOf_rotMap,
    Finset.sum_congr rfl fun d hd => bevalAt_sjsuIntChunks (Finset.mem_range.1 hd) _ _]

end KAM.EffectiveStability.SJSU

end
