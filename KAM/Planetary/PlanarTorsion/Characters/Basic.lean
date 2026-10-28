/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Factor

/-!
# Planar quartic torsion: character decomposition

Blueprint P, Part 11b (`bpP:p11b:char`, steps `ch-mon`, `ch-bra`): covariance, finite mode
support, reconstruction and reality of the characters of a quartic family.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.Planetary.PlanarCharacters

lemma charIdx_sum {a : Fin 4 → Fin 5} (ha : a ∈ charIdx) :
    (a 0).val + (a 1).val + ((a 2).val + (a 3).val) = 4 := by
  simp only [charIdx, Finset.mem_filter, Finset.mem_univ, true_and, Fin.sum_univ_four] at ha
  omega

lemma sum_piFinset_two (A B : ℤ → ℂ) (D : ℤ) :
    ∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-D) D), A (k 0) * B (k 1) =
      (∑ j ∈ Finset.Icc (-D) D, A j) * ∑ j ∈ Finset.Icc (-D) D, B j := by
  have := Finset.prod_univ_sum (fun _ : Fin 2 => Finset.Icc (-D) D) (fun i j => ![A, B] i j)
  simpa [Fin.prod_univ_two] using this.symm

lemma character_support {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (I : Fin 2 → ℝ)
    (z : Phase 2) (k : Fin 2 → ℤ) (hk : 4 < (∑ i, |(k i : ℝ)|)) :
    p11c_character F.eval k I z = 0 := by
  rw [character_eq_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  have h4 := charIdx_sum ha
  have hk' : (4 : ℤ) < |k 0| + |k 1| := by
    rw [Fin.sum_univ_two] at hk
    have : (4 : ℝ) < ((|k 0| + |k 1| : ℤ) : ℝ) := by push_cast; simpa using hk
    exact_mod_cast this
  by_cases h0 : (((a 0).val + (a 1).val : ℕ) : ℤ) < |k 0|
  · rw [charFc_eq_zero_of_lt _ _ _ _ _ h0]; simp
  · have h1 : (((a 2).val + (a 3).val : ℕ) : ℤ) < |k 1| := by push_cast at h0 ⊢; omega
    rw [charFc_eq_zero_of_lt _ _ _ _ _ h1]; simp

lemma character_covariance {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (I : Fin 2 → ℝ)
    (z : Phase 2) (theta : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    p11c_character F.eval k I (p11c_rotation theta z) =
      Complex.exp (Complex.I * (∑ j, (k j : ℂ) * theta j)) * p11c_character F.eval k I z := by
  rw [character_eq_sum, character_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [p11c_rotation]
  rw [charFc_rot, charFc_rot]
  have : Complex.exp (Complex.I * (∑ j, (k j : ℂ) * theta j)) =
      Complex.exp (Complex.I * ((k 0 : ℂ) * theta 0)) * Complex.exp (Complex.I * ((k 1 : ℂ) * theta 1)) := by
    rw [Fin.sum_univ_two, mul_add, Complex.exp_add]
  rw [this]; ring

theorem char {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) :
    (∀ I z theta k, p11c_character F.eval k I (p11c_rotation theta z) =
      Complex.exp (Complex.I * (∑ j, (k j : ℂ) * theta j)) * p11c_character F.eval k I z) ∧
    (∀ I z k, 4 < (∑ i, |(k i : ℝ)|) → p11c_character F.eval k I z = 0) ∧
    (∀ I z, HasSum (fun k => p11c_character F.eval k I z) (F.eval I z : ℂ)) ∧
    (∀ I z k, star (p11c_character F.eval k I z) = p11c_character F.eval (-k) I z) := by
  refine ⟨fun I z theta k => character_covariance F I z theta k,
    fun I z k hk => character_support F I z k hk, ?_, ?_⟩
  · intro I z
    have hsupp : ∀ k ∉ Fintype.piFinset
        (fun _ : Fin 2 => Finset.Icc (-((4 : ℕ) : ℤ)) ((4 : ℕ) : ℤ)),
        p11c_character F.eval k I z = 0 := by
      intro k hk
      apply character_support F I z k
      rw [Fintype.mem_piFinset] at hk
      push_neg at hk
      obtain ⟨i, hi⟩ := hk
      rw [Finset.mem_Icc] at hi
      have h1 : (4 : ℝ) < |(k i : ℝ)| := by
        have : (4 : ℤ) < |k i| := by push_cast at hi; rw [lt_abs]; omega
        exact_mod_cast this
      exact h1.trans_le (Finset.single_le_sum (f := fun j => |(k j : ℝ)|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    refine (?_ : _ = (F.eval I z : ℂ)) ▸ hasSum_sum_of_ne_finset_zero hsupp
    simp_rw [character_eq_sum]
    rw [Finset.sum_comm]
    unfold QuarticFamily.eval
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum, sum_piFinset_two (fun j => charFc ((a 0).val) ((a 1).val) (z.1 0) (z.2 0) j)
      (fun j => charFc ((a 2).val) ((a 3).val) (z.1 1) (z.2 1) j),
      charFc_sum _ _ _ (by have := charIdx_sum ha; omega),
      charFc_sum _ _ _ (by have := charIdx_sum ha; omega)]
    simp only [p11c_monomial]
    push_cast; ring
  · intro I z k
    unfold p11c_character
    rw [star_mul']
    have e : star ((2 * π : ℂ) ^ (-2 : ℤ)) = (2 * π : ℂ) ^ (-2 : ℤ) := by
      simp
    rw [e]
    congr 1
    show (starRingEnd ℂ) _ = _
    rw [← integral_conj]
    congr 1; ext θ
    simp only [map_mul, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    congr 2
    simp [map_sum, Finset.sum_neg_distrib]
    ring

end KAM.Planetary

end
