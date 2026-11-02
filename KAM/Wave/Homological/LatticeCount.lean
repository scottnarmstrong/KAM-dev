/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.LatticeCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact count of `ℓ¹` spheres in `ℤ²` (blueprint-W `bpW:w4:lattice` (i))

For `N ≥ 1`, exactly `4N` points `k ∈ ℤ²` satisfy `|k₁| + |k₂| = N`
(`waveSphere_card`, `waveLattice_ncard_fiber`). The finset form `waveLattice_card_filter_le`
bounds the number of points of any finset of `ℤ²` in the sphere.
-/

@[expose] public section

namespace KAM.Wave

open Finset

/-- The `ℓ¹` sphere of radius `N` in `ℤ × ℤ`, inside the box `[-N, N]²`. -/
def waveSphere (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(N : ℤ)) N) ×ˢ (Icc (-(N : ℤ)) N)).filter fun p => p.1.natAbs + p.2.natAbs = N

theorem waveSphere_fiber_card_eq (N : ℕ) (a : ℤ) (ha : a ∈ Icc (-(N : ℤ)) N)
    (h : a.natAbs = N) : ((waveSphere N).filter fun p => p.1 = a).card = 1 := by
  rw [mem_Icc] at ha
  have hset : (waveSphere N).filter (fun p => p.1 = a) = {(a, 0)} := by
    ext ⟨x, y⟩
    simp only [waveSphere, mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, hxy⟩, rfl⟩
      refine ⟨rfl, ?_⟩
      omega
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨⟨ha, ?_⟩, by simpa using h⟩, rfl⟩
      constructor <;> omega
  rw [hset]; simp

theorem waveSphere_fiber_card_lt (N : ℕ) (a : ℤ) (ha : a ∈ Icc (-(N : ℤ)) N)
    (h : a.natAbs ≠ N) : ((waveSphere N).filter fun p => p.1 = a).card = 2 := by
  rw [mem_Icc] at ha
  have hset : (waveSphere N).filter (fun p => p.1 = a) =
      {(a, (N : ℤ) - a.natAbs), (a, -((N : ℤ) - a.natAbs))} := by
    ext ⟨x, y⟩
    simp only [waveSphere, mem_filter, mem_product, mem_Icc, mem_insert, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, hxy⟩, rfl⟩
      omega
    · rintro (⟨rfl, hy⟩ | ⟨rfl, hy⟩) <;> refine ⟨⟨⟨ha, ?_⟩, ?_⟩, rfl⟩
      · constructor <;> omega
      · omega
      · constructor <;> omega
      · omega
  rw [hset, card_insert_of_notMem]
  · simp
  · simp only [mem_singleton, Prod.mk.injEq, true_and]
    omega

/-- The sphere `|k₁| + |k₂| = N` in `ℤ²` has `4N` points for `N ≥ 1`
(blueprint `bpW:w4:lattice` (i)). -/
theorem waveSphere_card (N : ℕ) (hN : 1 ≤ N) : (waveSphere N).card = 4 * N := by
  have hmaps : ∀ p ∈ waveSphere N, p.1 ∈ Icc (-(N : ℤ)) N := by
    intro p hp
    simp only [waveSphere, mem_filter, mem_product] at hp
    exact hp.1.1
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ a ∈ Icc (-(N : ℤ)) N,
      ((waveSphere N).filter fun p => p.1 = a).card = 2 - if a.natAbs = N then 1 else 0 := by
    intro a ha
    by_cases h : a.natAbs = N
    · rw [waveSphere_fiber_card_eq N a ha h]; simp [h]
    · rw [waveSphere_fiber_card_lt N a ha h]; simp [h]
  rw [sum_congr rfl hfib]
  have h2 : (Icc (-(N : ℤ)) N).filter (fun a => a.natAbs = N) =
      ({-(N : ℤ), (N : ℤ)} : Finset ℤ) := by
    ext a
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    omega
  have hcard : (Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
    simp; omega
  have hadd : ∑ a ∈ Icc (-(N : ℤ)) N, (2 - if a.natAbs = N then 1 else 0) +
      ∑ a ∈ Icc (-(N : ℤ)) N, (if a.natAbs = N then 1 else 0) = 2 * (2 * N + 1) := by
    rw [← sum_add_distrib, sum_congr rfl (fun a _ => (by split_ifs <;> omega :
      (2 - if a.natAbs = N then 1 else 0) + (if a.natAbs = N then 1 else 0) = 2)),
      sum_const, hcard]
    simp [mul_comm]
  have hite : ∑ a ∈ Icc (-(N : ℤ)) N, (if a.natAbs = N then 1 else 0) = 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, h2, card_insert_of_notMem]
    · simp
    · simp; omega
  omega

end KAM.Wave
