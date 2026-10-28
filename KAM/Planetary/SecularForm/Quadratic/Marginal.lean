/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Momentum

/-!
# Quadratic part: two-angle marginals of the cell average

Blueprint P, Part 8, `stepP:p8:qf-pair` (package S8-Q), measure-theoretic half. The average over
the angle cell `[0, 2π]ⁿ` of a function of two coordinates `(tᵢ, tⱼ)`, `i ≠ j`, is the average of
that function over `[0, 2π]²` (the coordinates are independent for the normalised product
measure). No integrability is assumed.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function ProbabilityTheory
open scoped BigOperators Topology ENNReal
namespace KAM.Planetary
namespace SecularForm
variable {n : ℕ}

/-- Normalised Lebesgue measure on `[0, 2π]`. -/
def angleLaw : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Icc 0 (2 * π))

instance : IsProbabilityMeasure angleLaw := by
  refine ⟨?_⟩
  simp only [angleLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top

theorem pi_angleLaw (n : ℕ) :
    Measure.pi (fun _ : Fin n => angleLaw) =
      ((ENNReal.ofReal (2 * π))⁻¹ ^ n) • volume.restrict (cell n) := by
  rw [cell, volume_pi, Measure.restrict_pi_pi]
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, angleLaw, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem avg_eq_integral_angleLaw (f : Vec n → ℝ) :
    avg f = ∫ t, f t ∂(Measure.pi fun _ : Fin n => angleLaw) := by
  rw [pi_angleLaw, integral_smul_measure]
  unfold avg
  have h : (((ENNReal.ofReal (2 * π))⁻¹ ^ n : ℝ≥0∞)).toReal = (2 * π) ^ (-(n : ℤ)) := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), zpow_neg,
      zpow_natCast, inv_pow]
  rw [h, smul_eq_mul]

/-- The average of a function of two coordinates is its average over `[0, 2π]²`. -/
theorem avg_pair_marginal {i j : Fin n} (hij : i ≠ j) {g : Vec 2 → ℝ}
    (hg : ContinuousOn g (cell 2)) : avg (fun t : Vec n => g ![t i, t j]) = avg g := by
  classical
  set P : Measure (Vec n) := Measure.pi fun _ : Fin n => angleLaw with hP
  set P2 : Measure (Vec 2) := Measure.pi fun _ : Fin 2 => angleLaw with hP2
  rw [avg_eq_integral_angleLaw, avg_eq_integral_angleLaw]
  have hind : iIndepFun (fun (k : Fin n) (ω : Vec n) => ω k) P :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hind2 := hind.indepFun hij
  have hmap : P.map (fun ω => (ω i, ω j)) = angleLaw.prod angleLaw := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable).1 hind2]
    simp only [hP, Measure.pi_map_eval]
    simp
  set e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ) with he
  have hmp : P2.map e = angleLaw.prod angleLaw := by
    have := (measurePreserving_piFinTwo (fun _ : Fin 2 => angleLaw)).map_eq
    simpa [he, hP2] using this
  have hg' : AEStronglyMeasurable g P2 := by
    rw [hP2, pi_angleLaw]
    exact (hg.aestronglyMeasurable measurableSet_cell).smul_measure _
  set f : ℝ × ℝ → ℝ := fun p => g ![p.1, p.2] with hf
  have hfe : f ∘ e = g := by
    funext x
    simp only [hf, he, comp_apply, MeasurableEquiv.piFinTwo_apply]
    congr 1
    ext k; fin_cases k <;> rfl
  have hf2 : AEStronglyMeasurable f (angleLaw.prod angleLaw) := by
    rw [← hmp, e.measurableEmbedding.aestronglyMeasurable_map_iff, hfe]
    exact hg'
  have hpair : AEMeasurable (fun ω : Vec n => (ω i, ω j)) P :=
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
  calc ∫ t, g ![t i, t j] ∂P = ∫ t, f ((fun ω : Vec n => (ω i, ω j)) t) ∂P := rfl
    _ = ∫ p, f p ∂(P.map fun ω : Vec n => (ω i, ω j)) :=
        (integral_map hpair (by rw [hmap]; exact hf2)).symm
    _ = ∫ p, f p ∂(P2.map e) := by rw [hmap, hmp]
    _ = ∫ x, f (e x) ∂P2 := integral_map e.measurable.aemeasurable (by rw [hmp]; exact hf2)
    _ = ∫ x, g x ∂P2 := by rw [← hfe]; rfl

end SecularForm
end KAM.Planetary
end
