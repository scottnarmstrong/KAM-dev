/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Finsupp.Single
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finitely supported integer vectors of small `ℓ¹` norm (for blueprint `bpW:w0n:nondeg`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`KAM.Wave.l1Norm l = ∑ j, |l_j|` for `l : ℕ →₀ ℤ` (the index `j` stands for the normal mode
`j + 3`). A vector of `ℓ¹` norm `1` is `±e_ν`; of norm `2` it is `±2e_ν` or `±e_a ± e_b`, `a ≠ b`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The `ℓ¹` norm `|l| = ∑ |l_j|` of a finitely supported integer vector. -/
def l1Norm (l : ℕ →₀ ℤ) : ℕ := l.sum fun _ v => v.natAbs

theorem l1Norm_eq_sum (l : ℕ →₀ ℤ) : l1Norm l = ∑ j ∈ l.support, (l j).natAbs := rfl

theorem card_support_le_l1Norm (l : ℕ →₀ ℤ) : l.support.card ≤ l1Norm l := by
  rw [l1Norm_eq_sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.2
    (by simpa using Finsupp.mem_support_iff.1 hj)

theorem l1Norm_one (l : ℕ →₀ ℤ) (h : l1Norm l = 1) :
    ∃ ν : ℕ, ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ l = Finsupp.single ν σ := by
  have hc : l.support.card = 1 := by
    have := card_support_le_l1Norm l
    have h0 : l.support.card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero, Finsupp.support_eq_empty] at h0
      subst h0; simp [l1Norm] at h
    omega
  obtain ⟨ν, hν⟩ := Finset.card_eq_one.1 hc
  refine ⟨ν, l ν, ?_, ?_⟩
  · rw [l1Norm_eq_sum, hν] at h
    simp at h
    omega
  · exact Finsupp.eq_single_iff.2 ⟨by rw [hν], rfl⟩

theorem l1Norm_two (l : ℕ →₀ ℤ) (h : l1Norm l = 2) :
    (∃ ν : ℕ, ∃ σ : ℤ, (σ = 2 ∨ σ = -2) ∧ l = Finsupp.single ν σ) ∨
      ∃ a b : ℕ, ∃ σ τ : ℤ, a ≠ b ∧ (σ = 1 ∨ σ = -1) ∧ (τ = 1 ∨ τ = -1) ∧
        l = Finsupp.single a σ + Finsupp.single b τ := by
  have hle := card_support_le_l1Norm l
  have hpos : ∀ j ∈ l.support, 1 ≤ (l j).natAbs := fun j hj =>
    Nat.one_le_iff_ne_zero.2 (by simpa using Finsupp.mem_support_iff.1 hj)
  have hc : l.support.card = 1 ∨ l.support.card = 2 := by
    have h0 : l.support.card ≠ 0 := by
      intro h0
      rw [Finset.card_eq_zero, Finsupp.support_eq_empty] at h0
      subst h0; simp [l1Norm] at h
    omega
  rcases hc with hc | hc
  · left
    obtain ⟨ν, hν⟩ := Finset.card_eq_one.1 hc
    refine ⟨ν, l ν, ?_, Finsupp.eq_single_iff.2 ⟨by rw [hν], rfl⟩⟩
    rw [l1Norm_eq_sum, hν] at h
    simp at h
    omega
  · right
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hc
    have ha : a ∈ l.support := by rw [hs]; simp
    have hb : b ∈ l.support := by rw [hs]; simp
    have h1 := hpos a ha
    have h2 := hpos b hb
    rw [l1Norm_eq_sum, hs, Finset.sum_pair hab] at h
    refine ⟨a, b, l a, l b, hab, by omega, by omega, ?_⟩
    ext j
    by_cases hja : j = a
    · subst hja; simp [hab]
    · by_cases hjb : j = b
      · subst hjb; simp [Ne.symm hab]
      · have : j ∉ l.support := by rw [hs]; simp [hja, hjb]
        rw [Finsupp.notMem_support_iff.1 this]
        simp [Ne.symm hja, Ne.symm hjb]

end KAM.Wave

end
