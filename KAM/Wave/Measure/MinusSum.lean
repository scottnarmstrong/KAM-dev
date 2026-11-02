/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.MinusZones
public import KAM.Wave.Measure.RealBounds

/-!
# W7: the union over `Λ⁻` at fixed `k` (blueprint `bpW:w7:prep`, `bpW:w7:iter`, steps "`Λ⁻`, sum
over `n` and sign")

`minus_assembly`: the zone of `(k, -l)` is the zone of `(-k, l)`, so the union over `Λ⁻ ∖ X` at
fixed `k` is covered by the unions for `±k` over `l = e_{j+n} - e_j`, `1 ≤ n ≤ |k|/ϑ`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

/-- `e_{j+n} - e_j`. -/
def lamMinusPlus (j n : ℕ) : ℕ →₀ ℤ := single (j + n) 1 + single j (-1)

theorem l1Norm_neg (l : ℕ →₀ ℤ) : l1Norm (-l) = l1Norm l := by
  rw [l1Norm_eq_sum, l1Norm_eq_sum, Finsupp.support_neg]
  exact Finset.sum_congr rfl fun j _ => by simp

theorem isLam_neg {l : ℕ →₀ ℤ} (h : IsLam l) : IsLam (-l) := by
  unfold IsLam at *; rw [l1Norm_neg]; exact h

theorem measXSet_neg {m : ℝ} {hm : 0 < m} {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ}
    (h : (k, l) ∈ measXSet m hm) : (-k, -l) ∈ measXSet m hm := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isLam_neg h1, ?_, ?_, ?_, ?_⟩
  · rw [kAbs_neg]; exact h2
  · rw [kAbs_neg]; exact h3
  · rw [japL_neg]; exact h4
  · have hs : {ν | (-l) ν ≠ 0} = {ν | l ν ≠ 0} := by ext ν; simp
    simp only [hs]
    rcases h5 with h5 | h5
    · left; rwa [isLamMinus_neg_iff]
    · right; exact h5

theorem measXSet_neg_iff {m : ℝ} {hm : 0 < m} {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} :
    (-k, -l) ∈ measXSet m hm ↔ (k, l) ∈ measXSet m hm :=
  ⟨fun h => by simpa using measXSet_neg h, measXSet_neg⟩

/-- Every `l ∈ Λ⁻` is `±(e_{j+n} - e_j)`. -/
theorem isLamMinus_cases {l : ℕ →₀ ℤ} (h : IsLamMinus l) :
    ∃ j n : ℕ, 1 ≤ n ∧ (l = lamMinusPlus j n ∨ l = -lamMinusPlus j n) := by
  obtain ⟨i, j, σ, hji, hσ, rfl⟩ := h
  refine ⟨j, i - j, by omega, ?_⟩
  have : j + (i - j) = i := by omega
  rcases hσ with rfl | rfl
  · left; simp [lamMinusPlus, this]
  · right; simp [lamMinusPlus, this]; abel

section

variable (m : ℝ) (hm : 0 < m)

/-- The union over `Λ⁻ ∖ X` at fixed `k` for a family of zones `Z`. -/
def minusUnion (Z : (Fin 2 → ℤ) → (ℕ →₀ ℤ) → Set (Fin 2 → ℝ)) (k : Fin 2 → ℤ) :
    Set (Fin 2 → ℝ) :=
  ⋃ (l : ℕ →₀ ℤ) (_ : IsLamMinus l ∧ (k, l) ∉ measXSet m hm), Z k l

theorem minus_assembly (Z : (Fin 2 → ℤ) → (ℕ →₀ ℤ) → Set (Fin 2 → ℝ))
    (hsym : ∀ k l, Z k (-l) = Z (-k) l) {k : Fin 2 → ℤ} (hk : k ≠ 0) {c1 c0 : ℝ}
    (hc1 : 0 ≤ c1) (hc0 : 0 ≤ c0)
    (hNe : ∀ k' : Fin 2 → ℤ, kAbs k' = kAbs k → ∀ j n : ℕ, (Z k' (lamMinusPlus j n)).Nonempty →
      (n : ℝ) ≤ kAbs k / measTheta m hm)
    (hn : ∀ k' : Fin 2 → ℤ, kAbs k' = kAbs k → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ kAbs k / measTheta m hm →
      volume (⋃ (j : ℕ) (_ : (k', lamMinusPlus j n) ∉ measXSet m hm), Z k' (lamMinusPlus j n)) ≤
        ENNReal.ofReal (c1 * n + c0)) :
    volume (minusUnion m hm Z k) ≤ ENNReal.ofReal
      (2 * (c1 * (kAbs k / measTheta m hm) ^ 2 + c0 * (kAbs k / measTheta m hm))) := by
  classical
  have hϑ := measTheta_pos m hm
  have hk1 := one_le_kAbs hk
  set x : ℝ := kAbs k / measTheta m hm with hx
  have hx0 : 0 ≤ x := by positivity
  set N : ℕ := ⌊x⌋₊ with hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  -- the cover
  set W : (Fin 2 → ℤ) → Set (Fin 2 → ℝ) := fun k' =>
    ⋃ n ∈ Finset.Icc 1 N, ⋃ (j : ℕ) (_ : (k', lamMinusPlus j n) ∉ measXSet m hm),
      Z k' (lamMinusPlus j n) with hW
  have hsub : minusUnion m hm Z k ⊆ W k ∪ W (-k) := by
    intro ξ hξ
    simp only [minusUnion, Set.mem_iUnion] at hξ
    obtain ⟨l, ⟨hl, hX⟩, hz⟩ := hξ
    obtain ⟨j, n, hn1, hcase⟩ := isLamMinus_cases hl
    rcases hcase with rfl | rfl
    · have hne : (Z k (lamMinusPlus j n)).Nonempty := ⟨ξ, hz⟩
      have hnN : n ≤ N := Nat.le_floor (hNe k rfl j n hne)
      left
      simp only [hW, Set.mem_iUnion]
      exact ⟨n, Finset.mem_Icc.2 ⟨hn1, hnN⟩, j, hX, hz⟩
    · rw [hsym] at hz
      have hX' : (-k, lamMinusPlus j n) ∉ measXSet m hm := fun h => hX (by
        have := measXSet_neg h
        simpa using this)
      have hne : (Z (-k) (lamMinusPlus j n)).Nonempty := ⟨ξ, hz⟩
      have hnN : n ≤ N := Nat.le_floor (hNe (-k) (kAbs_neg k) j n hne)
      right
      simp only [hW, Set.mem_iUnion]
      exact ⟨n, Finset.mem_Icc.2 ⟨hn1, hnN⟩, j, hX', hz⟩
  have hWbound : ∀ k' : Fin 2 → ℤ, kAbs k' = kAbs k →
      volume (W k') ≤ ENNReal.ofReal (c1 * x ^ 2 + c0 * x) := by
    intro k' hk'
    calc volume (W k') ≤ ∑ n ∈ Finset.Icc 1 N, volume (⋃ (j : ℕ)
          (_ : (k', lamMinusPlus j n) ∉ measXSet m hm), Z k' (lamMinusPlus j n)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ENNReal.ofReal (c1 * n + c0) := by
          refine Finset.sum_le_sum fun n hn' => ?_
          have h1 := (Finset.mem_Icc.1 hn').1
          have h2 : (n : ℝ) ≤ x := by
            have : n ≤ N := (Finset.mem_Icc.1 hn').2
            exact (Nat.cast_le.2 this).trans hNx
          exact hn k' hk' n h1 h2
      _ = ENNReal.ofReal (∑ n ∈ Finset.Icc 1 N, (c1 * n + c0)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
      _ ≤ ENNReal.ofReal (c1 * x ^ 2 + c0 * x) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hs : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ≤ (N : ℝ) ^ 2 := by
            have : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ≤ ∑ _n ∈ Finset.Icc 1 N, (N : ℝ) :=
              Finset.sum_le_sum fun n hn' => by exact_mod_cast (Finset.mem_Icc.1 hn').2
            refine this.trans ?_
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            have : ((N + 1 - 1 : ℕ) : ℝ) = N := by simp
            rw [this]; ring_nf; exact le_rfl
          have hc : ∑ _n ∈ Finset.Icc 1 N, c0 = c0 * N := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            simp [mul_comm]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc]
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have : (N : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
          nlinarith
  calc volume (minusUnion m hm Z k) ≤ volume (W k ∪ W (-k)) := measure_mono hsub
    _ ≤ volume (W k) + volume (W (-k)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (c1 * x ^ 2 + c0 * x) + ENNReal.ofReal (c1 * x ^ 2 + c0 * x) :=
        add_le_add (hWbound k rfl) (hWbound (-k) (kAbs_neg k))
    _ = ENNReal.ofReal (2 * (c1 * x ^ 2 + c0 * x)) := by
        rw [← two_mul, ENNReal.ofReal_mul (by norm_num)]; simp

end

end KAM.Wave

end
