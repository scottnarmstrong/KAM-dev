/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic

/-!
# Secular form: the angle average of a function of two angles

Blueprint P, Part 8, `stepP:p8:q4-str` (pair decomposition): the average over the cell of a
continuous function of two distinct angles `t j`, `t k` is the iterated normalised double integral.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary

namespace SecularForm

variable {n : ℕ}

private theorem prod_pair_ite {α : Type*} [CommMonoid α] {j k : Fin n} (hjk : j ≠ k)
    (a b c : α) :
    ∏ l : Fin n, (if l = j then a else if l = k then b else c) = a * b * c ^ (n - 2) := by
  have h1 : ∏ l : Fin n, (if l = j then a else if l = k then b else c) =
      a * ∏ l ∈ Finset.univ.erase j, (if l = k then b else c) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun l : Fin n => if l = j then a else if l = k then b else c) (Finset.mem_univ j)]
    simp only [ite_true]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    simp [Finset.ne_of_mem_erase hl]
  have hk : k ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hjk.symm, Finset.mem_univ k⟩
  have h2 : ∏ l ∈ Finset.univ.erase j, (if l = k then b else c) =
      b * ∏ l ∈ (Finset.univ.erase j).erase k, (if l = k then b else c) := by
    rw [← Finset.mul_prod_erase _ (fun l : Fin n => if l = k then b else c) hk]; simp
  have h3 : ∏ l ∈ (Finset.univ.erase j).erase k, (if l = k then b else c) = c ^ (n - 2) := by
    rw [Finset.prod_congr rfl (fun l hl => by rw [ite_eq_right_iff.2 fun h => absurd h (Finset.ne_of_mem_erase hl)]),
      Finset.prod_const, Finset.card_erase_of_mem hk, Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp; congr 1
  rw [h1, h2, h3, mul_assoc]

private theorem map_pi_pair {j k : Fin n} (hjk : j ≠ k) :
    (Measure.pi fun _ : Fin n => volume.restrict (Icc (0:ℝ) (2 * π))).map
        (fun t : Fin n → ℝ => (t j, t k)) =
      (ENNReal.ofReal (2 * π)) ^ (n - 2) •
        (volume.restrict (Icc (0:ℝ) (2 * π))).prod (volume.restrict (Icc (0:ℝ) (2 * π))) := by
  set ν : Measure ℝ := volume.restrict (Icc (0:ℝ) (2 * π)) with hν
  set c : ENNReal := (ENNReal.ofReal (2 * π)) ^ (n - 2) with hc
  have hνu : ν univ = ENNReal.ofReal (2 * π) := by
    rw [hν, Measure.restrict_apply_univ, Real.volume_Icc]; simp
  have hc0 : c ≠ 0 := pow_ne_zero _ (by simp [Real.pi_pos])
  have hct : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hmeas : Measurable fun t : Fin n → ℝ => (t j, t k) := by fun_prop
  have h : ν.prod ν = c⁻¹ • (Measure.pi fun _ : Fin n => ν).map fun t => (t j, t k) := by
    refine Measure.prod_eq fun A B hA hB => ?_
    rw [Measure.smul_apply, Measure.map_apply hmeas (hA.prod hB)]
    have hpre : (fun t : Fin n → ℝ => (t j, t k)) ⁻¹' (A ×ˢ B) =
        Set.pi univ (fun l => if l = j then A else if l = k then B else univ) := by
      ext t
      simp only [mem_preimage, mem_prod, Set.mem_pi, mem_univ, true_implies]
      constructor
      · rintro ⟨h1, h2⟩ l
        by_cases hlj : l = j
        · subst hlj; simpa using h1
        · by_cases hlk : l = k
          · subst hlk; simpa [hlj] using h2
          · simp [hlj, hlk]
      · intro h
        refine ⟨?_, ?_⟩
        · simpa using h j
        · simpa [hjk.symm] using h k
    rw [hpre, Measure.pi_pi]
    have : ∀ l : Fin n, ν (if l = j then A else if l = k then B else univ) =
        if l = j then ν A else if l = k then ν B else ν univ := fun l => by
      split_ifs <;> rfl
    simp_rw [this]
    rw [prod_pair_ite hjk, hνu]
    simp only [smul_eq_mul]
    rw [← hc]
    calc c⁻¹ * (ν A * ν B * c) = (c⁻¹ * c) * (ν A * ν B) := by ring
      _ = ν A * ν B := by rw [ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [h, smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]

/-- The cell average of a continuous function of two distinct angles is the iterated normalised
double integral. -/
theorem avg_pair {j k : Fin n} (hjk : j ≠ k) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 (2 * π) ×ˢ Icc 0 (2 * π))) :
    avg (fun t : Vec n => g (t j) (t k)) =
      (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π, g s t := by
  set ν : Measure ℝ := volume.restrict (Icc (0:ℝ) (2 * π)) with hν
  have hmeas : Measurable fun t : Fin n → ℝ => (t j, t k) := by fun_prop
  have hcell : (volume.restrict (cell n) : Measure (Fin n → ℝ)) = Measure.pi fun _ => ν := by
    unfold cell
    rw [volume_pi, Measure.restrict_pi_pi]
  have hint : Integrable (fun p : ℝ × ℝ => g p.1 p.2) (ν.prod ν) := by
    have : ν.prod ν = (volume.prod volume).restrict (Icc (0:ℝ) (2 * π) ×ˢ Icc (0:ℝ) (2 * π)) := by
      rw [hν, Measure.prod_restrict]
    rw [this]
    exact (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
  have h1 : ∫ t in cell n, g (t j) (t k) =
      (2 * π) ^ (n - 2) * ∫ p, g p.1 p.2 ∂(ν.prod ν) := by
    rw [hcell]
    have := integral_map hmeas.aemeasurable (f := fun p : ℝ × ℝ => g p.1 p.2)
      (μ := Measure.pi fun _ : Fin n => ν)
      (by rw [map_pi_pair hjk]; exact hint.1.smul_measure _)
    simp only at this
    rw [← this, map_pi_pair hjk, integral_smul_measure, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have h2 : ∫ p, g p.1 p.2 ∂(ν.prod ν) =
      ∫ s in (0:ℝ)..2 * π, ∫ t in (0:ℝ)..2 * π, g s t := by
    rw [integral_prod _ hint]
    simp only [hν, intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π),
      integral_Icc_eq_integral_Ioc]
  have h3 : ((2 * π) ^ (-(n : ℤ)) : ℝ) * (2 * π) ^ (n - 2) = (2 * π)⁻¹ * (2 * π)⁻¹ := by
    have hn : 2 ≤ n := by
      have := j.2; have := k.2
      by_contra h
      push Not at h
      exact hjk (Fin.ext (by omega))
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hπ : (2 * π) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel]
    rw [zpow_neg, zpow_natCast, pow_add]
    field_simp
  unfold avg
  rw [smul_eq_mul, h1, ← mul_assoc, h3, h2, mul_assoc, ← intervalIntegral.integral_const_mul]

end SecularForm
end KAM.Planetary
end
