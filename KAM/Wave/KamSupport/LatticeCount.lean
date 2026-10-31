/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Fourier.Derivative
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Counting lattice points of fixed `ℓ¹` size (blueprint-W `bpW:w1:lattice` (ii))

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

`kamL1 k = ∑ᵢ |kᵢ|` is the natural-number `ℓ¹` size of `k ∈ ℤⁿ`. For `n ≥ 1` the number of `k ∈ ℤⁿ`
with `kamL1 k = m` is at most `2ⁿ · C(m+n-1, n-1) ≤ 2ⁿ (m+1)^(n-1)`: `k` is determined by the
multiset of its coordinate absolute values (an element of `Sym (Fin n) m`, counted by
`Sym.card_sym_eq_choose`) and by the signs of its coordinates.
-/

@[expose] public section

namespace KAM.Wave

open Finset

variable {n : ℕ}

/-- The natural-number `ℓ¹` size `∑ᵢ |kᵢ|` of `k ∈ ℤⁿ`. -/
def kamL1 (k : Fin n → ℤ) : ℕ := ∑ i, (k i).natAbs

theorem kamL1_cast_eq_modeSize (k : Fin n → ℤ) : (kamL1 k : ℝ) = Fourier.modeSize k := by
  simp [kamL1, Fourier.modeSize, Nat.cast_sum]

/-- The multiset of coordinate absolute values. -/
def kamAbsMultiset (k : Fin n → ℤ) : Multiset (Fin n) :=
  ∑ i, (k i).natAbs • ({i} : Multiset (Fin n))

theorem kamAbsMultiset_count (k : Fin n → ℤ) (i : Fin n) :
    (kamAbsMultiset k).count i = (k i).natAbs := by
  simp [kamAbsMultiset, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]

theorem kamAbsMultiset_card (k : Fin n → ℤ) : Multiset.card (kamAbsMultiset k) = kamL1 k := by
  simp [kamAbsMultiset, kamL1]

/-- The code `k ↦ (signs, absolute values)`. -/
def kamLatticeCode (k : Fin n → ℤ) : (Fin n → Bool) × Multiset (Fin n) :=
  (fun i => decide (k i < 0), kamAbsMultiset k)

theorem kamLatticeCode_injective : Function.Injective (kamLatticeCode (n := n)) := by
  intro k l h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  funext i
  have hs := congrFun h1 i
  simp only [kamLatticeCode, decide_eq_decide] at hs
  have hc : (k i).natAbs = (l i).natAbs := by
    rw [← kamAbsMultiset_count k i, ← kamAbsMultiset_count l i]
    exact congrArg (fun M => Multiset.count i M) h2
  omega

/-- The number of `k ∈ s` of `ℓ¹` size `m` is at most `2ⁿ C(m+n-1, m)`. -/
theorem kamLattice_card_filter_le (s : Finset (Fin n → ℤ)) (m : ℕ) :
    (s.filter fun k => kamL1 k = m).card ≤ 2 ^ n * Nat.choose (n + m - 1) m := by
  classical
  let T : Finset (Multiset (Fin n)) :=
    (Finset.univ : Finset (Sym (Fin n) m)).image (fun t : Sym (Fin n) m => t.1)
  have hT : T.card ≤ Nat.choose (n + m - 1) m := by
    calc T.card ≤ (Finset.univ : Finset (Sym (Fin n) m)).card := Finset.card_image_le
      _ = Fintype.card (Sym (Fin n) m) := Finset.card_univ
      _ = Nat.choose (n + m - 1) m := by rw [Sym.card_sym_eq_choose]; simp
  have hmap : ∀ k ∈ s.filter (fun k => kamL1 k = m),
      kamLatticeCode k ∈ (Finset.univ : Finset (Fin n → Bool)) ×ˢ T := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
    have hc : Multiset.card (kamAbsMultiset k) = m := by rw [kamAbsMultiset_card, hk']
    let t : Sym (Fin n) m := ⟨kamAbsMultiset k, hc⟩
    have ht : t ∈ (Finset.univ : Finset (Sym (Fin n) m)) := Finset.mem_univ t
    exact Finset.mem_image_of_mem (fun t : Sym (Fin n) m => t.1) ht
  calc (s.filter fun k => kamL1 k = m).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ T).card :=
        Finset.card_le_card_of_injOn kamLatticeCode hmap (kamLatticeCode_injective.injOn)
    _ = 2 ^ n * T.card := by simp [Finset.card_product]
    _ ≤ 2 ^ n * Nat.choose (n + m - 1) m := Nat.mul_le_mul_left _ hT

theorem kamLattice_fiber_finite (m : ℕ) : {k : Fin n → ℤ | kamL1 k = m}.Finite := by
  classical
  -- each coordinate lies in `[-m, m]`
  refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-(m : ℤ)) m)
    fun _ => Set.finite_Icc _ _).subset ?_
  intro k hk i _
  have hle : (k i).natAbs ≤ m := by
    rw [← (hk : kamL1 k = m)]
    exact Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  constructor <;> omega

/-- **Counting** (blueprint `bpW:w1:lattice` (ii)): for `n ≥ 1`, the number of `k ∈ ℤⁿ` with
`|k|₁ = m` is at most `2ⁿ C(m+n-1, n-1)`. -/
theorem kamLattice_ncard_fiber_le (hn : 1 ≤ n) (m : ℕ) :
    {k : Fin n → ℤ | kamL1 k = m}.ncard ≤ 2 ^ n * Nat.choose (m + n - 1) (n - 1) := by
  classical
  have hfin := kamLattice_fiber_finite (n := n) m
  have := kamLattice_card_filter_le (hfin.toFinset) m
  have hfilt : hfin.toFinset.filter (fun k => kamL1 k = m) = hfin.toFinset := by
    ext k; simp
  rw [hfilt] at this
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine this.trans (Nat.mul_le_mul_left _ ?_)
  rw [show n + m - 1 = m + n - 1 by omega]
  rw [← Nat.choose_symm (by omega : n - 1 ≤ m + n - 1)]
  rw [show m + n - 1 - (n - 1) = m by omega]

/-- `C(m+j, j) ≤ (m+1)^j`. -/
theorem kamChoose_add_le_pow (m j : ℕ) : Nat.choose (m + j) j ≤ (m + 1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.add_one_mul_choose_eq (m + j) j
    have h2 : Nat.choose (m + j + 1) (j + 1) * (j + 1) ≤
        (m + 1) * Nat.choose (m + j) j * (j + 1) := by
      rw [← h]
      nlinarith [Nat.zero_le (Nat.choose (m + j) j), Nat.zero_le (m * j * Nat.choose (m + j) j)]
    have h3 := Nat.le_of_mul_le_mul_right h2 (Nat.succ_pos j)
    rw [show m + (j + 1) = m + j + 1 by ring, pow_succ]
    nlinarith [h3, ih, Nat.zero_le (m + 1)]

/-- **Counting** (blueprint `bpW:w1:lattice` (ii)), second inequality: the binomial count is at most
`2ⁿ (m+1)^(n-1)`. -/
theorem kamLattice_ncard_fiber_le_pow (hn : 1 ≤ n) (m : ℕ) :
    {k : Fin n → ℤ | kamL1 k = m}.ncard ≤ 2 ^ n * (m + 1) ^ (n - 1) := by
  refine (kamLattice_ncard_fiber_le hn m).trans (Nat.mul_le_mul_left _ ?_)
  have := kamChoose_add_le_pow m (n - 1)
  rwa [show m + n - 1 = m + (n - 1) by omega]

/-- Finset form of the fibre count used in the weighted sums: `n ≥ 1`. -/
theorem kamLattice_card_filter_le_pow (hn : 1 ≤ n) (s : Finset (Fin n → ℤ)) (m : ℕ) :
    (s.filter fun k => kamL1 k = m).card ≤ 2 ^ n * (m + 1) ^ (n - 1) := by
  refine (kamLattice_card_filter_le s m).trans (Nat.mul_le_mul_left _ ?_)
  have h := kamChoose_add_le_pow m (n - 1)
  rw [show n + m - 1 = m + (n - 1) by omega, Nat.choose_symm_add]
  exact h

end KAM.Wave
