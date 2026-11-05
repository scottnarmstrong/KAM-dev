/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Consts
public import Mathlib.NumberTheory.ZetaValues

/-!
# W7: lattice sums (blueprint `bpW:w7:ext-zeta`, `bpW:w7:count` (iii))

`#{k ∈ ℤ² : |k| = N} ≤ 4 N` for `N ≥ 1` and `∑_N N^{-2} = π²/6` give
`∑_{k ≠ 0} c |k|^{-3} ≤ c · 2π²/3 = c · Z₃`.
-/

@[expose] public noncomputable section

open Real MeasureTheory Set

namespace KAM.Wave

/-- The `ℓ¹` sphere `{k ∈ ℤ² : |k₁| + |k₂| = N}`. -/
def waveL1Sphere (N : ℕ) : Set (Fin 2 → ℤ) := {k | (k 0).natAbs + (k 1).natAbs = N}

theorem kAbs_eq_of_mem_l1Sphere {N : ℕ} {k : Fin 2 → ℤ} (hk : k ∈ waveL1Sphere N) :
    kAbs k = N := by
  simp only [waveL1Sphere, mem_ofPred_eq] at hk
  simp only [kAbs, Fin.sum_univ_two]
  rw [← hk]; push_cast
  have h : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := fun z => by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h, h]

/-- `#{k : |k| = N} ≤ 4 N`. -/
theorem encard_l1Sphere_le {N : ℕ} (hN : 1 ≤ N) : (waveL1Sphere N).encard ≤ 4 * N := by
  set f0 : ℕ → (Fin 2 → ℤ) := fun t => ![(t : ℤ), (N : ℤ) - t]
  set f1 : ℕ → (Fin 2 → ℤ) := fun t => ![-((N : ℤ) - t), (t : ℤ)]
  set f2 : ℕ → (Fin 2 → ℤ) := fun t => ![-(t : ℤ), -((N : ℤ) - t)]
  set f3 : ℕ → (Fin 2 → ℤ) := fun t => ![(N : ℤ) - t, -(t : ℤ)]
  set T : Finset (Fin 2 → ℤ) :=
    (Finset.range N).image f0 ∪ (Finset.range N).image f1 ∪ (Finset.range N).image f2 ∪
      (Finset.range N).image f3 with hT
  have hsub : waveL1Sphere N ⊆ (T : Set (Fin 2 → ℤ)) := by
    intro k hk
    simp only [waveL1Sphere, mem_ofPred_eq] at hk
    simp only [hT, Finset.coe_union, Finset.coe_image, Finset.coe_range, mem_union, mem_image,
      mem_Iio]
    have hk0 : k = ![k 0, k 1] := by ext i; fin_cases i <;> simp
    by_cases h1 : 0 ≤ k 0 ∧ 1 ≤ k 1
    · left; left; left
      refine ⟨(k 0).toNat, by omega, ?_⟩
      rw [hk0]; simp only [f0]
      ext i; fin_cases i <;> simp <;> omega
    · by_cases h2 : k 0 ≤ -1 ∧ 0 ≤ k 1
      · left; left; right
        refine ⟨(k 1).toNat, by omega, ?_⟩
        rw [hk0]; simp only [f1]
        ext i; fin_cases i <;> simp <;> omega
      · by_cases h3 : k 0 ≤ 0 ∧ k 1 ≤ -1
        · left; right
          refine ⟨(-(k 0)).toNat, by omega, ?_⟩
          rw [hk0]; simp only [f2]
          ext i; fin_cases i <;> simp <;> omega
        · right
          refine ⟨(-(k 1)).toNat, by omega, ?_⟩
          rw [hk0]; simp only [f3]
          ext i; fin_cases i <;> simp <;> omega
  calc (waveL1Sphere N).encard ≤ (T : Set (Fin 2 → ℤ)).encard := Set.encard_le_encard hsub
    _ = (T.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard T
    _ ≤ 4 * N := by
        have : T.card ≤ 4 * N := by
          calc T.card ≤ ((Finset.range N).image f0 ∪ (Finset.range N).image f1 ∪
                (Finset.range N).image f2).card + ((Finset.range N).image f3).card :=
                Finset.card_union_le _ _
            _ ≤ ((Finset.range N).image f0 ∪ (Finset.range N).image f1).card +
                ((Finset.range N).image f2).card + ((Finset.range N).image f3).card := by
                gcongr; exact Finset.card_union_le _ _
            _ ≤ ((Finset.range N).image f0).card + ((Finset.range N).image f1).card +
                ((Finset.range N).image f2).card + ((Finset.range N).image f3).card := by
                gcongr; exact Finset.card_union_le _ _
            _ ≤ N + N + N + N := by
                gcongr <;> exact (Finset.card_image_le).trans (by simp)
            _ = 4 * N := by ring
        exact_mod_cast this

/-- The lattice sum `∑_{k ≠ 0} c |k|^{-3} ≤ c Z₃` (blueprint `bpW:w7:count` (iii)). -/
theorem tsum_lattice_le {c : ℝ} (hc : 0 ≤ c) :
    ∑' k : Fin 2 → ℤ, (if k = 0 then 0 else ENNReal.ofReal (c / kAbs k ^ 3)) ≤
      ENNReal.ofReal (c * (2 * π ^ 2 / 3)) := by
  set F : (Fin 2 → ℤ) → ENNReal := fun k => if k = 0 then 0 else ENNReal.ofReal (c / kAbs k ^ 3)
    with hF
  have hsupp : Function.support F ⊆ ⋃ n : ℕ, waveL1Sphere (n + 1) := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => hk (by simp [hF, h])
    simp only [mem_iUnion]
    refine ⟨(k 0).natAbs + (k 1).natAbs - 1, ?_⟩
    have : 1 ≤ (k 0).natAbs + (k 1).natAbs := by
      by_contra h
      apply hk0
      have h0 : k 0 = 0 := by omega
      have h1 : k 1 = 0 := by omega
      ext i; fin_cases i <;> simp [h0, h1]
    simp only [waveL1Sphere, mem_ofPred_eq]
    omega
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine (ENNReal.tsum_iUnion_le_tsum F (fun n : ℕ => waveL1Sphere (n + 1))).trans ?_
  have hterm : ∀ n : ℕ, ∑' x : waveL1Sphere (n + 1), F x ≤
      ENNReal.ofReal (4 * c / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have hconst : ∀ x : waveL1Sphere (n + 1), F x = ENNReal.ofReal (c / ((n : ℝ) + 1) ^ 3) := by
      intro x
      have hx0 : (x : Fin 2 → ℤ) ≠ 0 := by
        intro h
        have := x.2
        simp only [waveL1Sphere, mem_ofPred_eq] at this
        rw [h] at this; simp at this
      simp only [hF, hx0, ↓reduceIte]
      rw [kAbs_eq_of_mem_l1Sphere x.2]; push_cast; rfl
    simp_rw [hconst]
    rw [ENNReal.tsum_set_const]
    have h4 := encard_l1Sphere_le (N := n + 1) (by omega)
    have : ((waveL1Sphere (n + 1)).encard : ENNReal) ≤ ENNReal.ofReal (4 * ((n : ℝ) + 1)) := by
      have h5 : ((waveL1Sphere (n + 1)).encard : ENNReal) ≤ ((4 * (n + 1) : ℕ∞) : ENNReal) := by
        exact_mod_cast h4
      refine h5.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
      norm_cast
    calc ((waveL1Sphere (n + 1)).encard : ENNReal) * ENNReal.ofReal (c / ((n : ℝ) + 1) ^ 3)
        ≤ ENNReal.ofReal (4 * ((n : ℝ) + 1)) * ENNReal.ofReal (c / ((n : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_right this zero_le
      _ = ENNReal.ofReal (4 * c / ((n : ℝ) + 1) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 (hasSum_zeta_two)
    simpa using this
  have hsum' : HasSum (fun n : ℕ => 4 * c / ((n : ℝ) + 1) ^ 2) (4 * c * (π ^ 2 / 6)) := by
    have := hsum.mul_left (4 * c)
    convert this using 1
    funext n; ring
  have hnn : ∀ n : ℕ, 0 ≤ 4 * c / ((n : ℝ) + 1) ^ 2 := fun n => by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum'.summable, hsum'.tsum_eq]
  refine le_of_eq ?_
  congr 1; ring

end KAM.Wave

end
