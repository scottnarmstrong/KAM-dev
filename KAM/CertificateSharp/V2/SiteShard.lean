/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.SmallDivQ

/-!
# A bite from shards

`balCheck` and `balBound` walk `2^l` fibres in one kernel computation. Its memory grows with the
number of fibres (about 0.8 MB per fibre, whatever the size of the box), so the cut-off `l = 12` of
a lunar bite needed 8–9 GB. The walk is a bisection, so it splits into blocks of `2^l₀` fibres:

* `shardOk d l₀ a u`: the fibre tests of one block, and a short rational bound `u` of its sum;
* `balAll_of_shards`, `balSum_le_of_shards`: the blocks give the whole walk;
* `biteOk_of_shards`: `biteOk … = true` from the blocks, each a kernel computation of its own, and
  a final rational comparison.

The test itself is unchanged: this is a way of proving `biteOk`, so a certificate that uses it
passes `siteOk` as it stands. The bounds `u` replace the exact accumulator, so the memory of one
block does not depend on the total.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp KAM.Sharp2.Examples

/-- A walk of `2^(l₀ + M)` steps from `2^M` blocks of `2^l₀` steps. -/
theorem balAll_of_shards (p : ℕ → Bool) (l₀ : ℕ) : ∀ (M a : ℕ),
    (∀ j < 2 ^ M, balAll p l₀ (a + j * 2 ^ l₀) = true) → balAll p (l₀ + M) a = true := by
  intro M
  induction M with
  | zero =>
    intro a h
    simpa using h 0 (by simp)
  | succ M ih =>
    intro a h
    rw [← add_assoc, balAll, Bool.and_eq_true]
    refine ⟨ih a fun j hj => h j (by rw [pow_succ]; omega), ih _ fun j hj => ?_⟩
    have := h (2 ^ M + j) (by rw [pow_succ]; omega)
    rwa [add_mul, ← pow_add, ← add_assoc, add_comm M l₀] at this

/-- The sum of a walk from bounds of its blocks. -/
theorem balSum_le_of_shards (f : ℕ → ℚ) (l₀ : ℕ) (u : ℕ → ℚ) : ∀ (M a j₀ : ℕ),
    (∀ j < 2 ^ M, balSum f l₀ (a + j * 2 ^ l₀) ≤ u (j₀ + j)) →
      balSum f (l₀ + M) a ≤ ∑ j ∈ Finset.range (2 ^ M), u (j₀ + j) := by
  intro M
  induction M with
  | zero =>
    intro a j₀ h
    simpa using h 0 (by simp)
  | succ M ih =>
    intro a j₀ h
    rw [← add_assoc, balSum, pow_succ, mul_two, Finset.sum_range_add]
    refine add_le_add (ih a j₀ fun j hj => h j (by omega)) ?_
    have key := ih (a + 2 ^ (l₀ + M)) (j₀ + 2 ^ M) fun j hj => by
      have := h (2 ^ M + j) (by omega)
      rwa [add_mul, ← pow_add, ← add_assoc, add_comm M l₀, ← add_assoc] at this
    refine key.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [add_assoc]

/-- The side conditions of `balCheck`. -/
def sideOk (d : SdsData) : Bool :=
  decide (0 < d.γ) && decide (0 < d.δ) && decide (0 < d.cLo) && decide (1 ≤ d.E1 * d.expLow)

/-- The block of `2^l₀` fibres from `a`: the tests of `balCheck`, and the bound `u` of its sum. -/
def shardOk (d : SdsData) (l₀ a : ℕ) (u : ℚ) : Bool :=
  balAll (fun j => fiberOk d (posMode j) && fiberOk d (negMode j)) l₀ a &&
    decide (balSum (fun j => fiberTerm d (posMode j) + fiberTerm d (negMode j)) l₀ a ≤ u)

/-- **`biteOk` from its blocks.** -/
theorem biteOk_of_shards {box : FreqBox} {κ γ b c : ℚ} {w : BiteWit} {l₀ M : ℕ}
    (hl : w.l = l₀ + M) (U : List ℚ) (hc : 0 < c) (hb : 0 < b)
    (hside : sideOk (biteData box κ γ b w) = true)
    (hs : ∀ j < 2 ^ M, shardOk (biteData box κ γ b w) l₀ (j * 2 ^ l₀) (U.getD j 0) = true)
    (hB : (biteData box κ γ b w).E1 * (99225 / 30000) +
        ∑ j ∈ Finset.range (2 ^ M), U.getD j 0 + (biteData box κ γ b w).tailBound ≤ w.B)
    (hnum : w.B * (κ ^ 2)⁻¹ * (γ * b) ^ 2 ≤ (31415 / 10000 * c) ^ 2) :
    biteOk box κ γ b c w = true := by
  set d := biteData box κ γ b w with hd
  simp only [shardOk, Bool.and_eq_true, decide_eq_true_eq] at hs
  have hA : balAll (fun j => fiberOk d (posMode j) && fiberOk d (negMode j)) w.l 0 = true := by
    rw [hl]
    exact balAll_of_shards _ l₀ M 0 fun j hj => by simpa using (hs j hj).1
  have hS : balSum (fun j => fiberTerm d (posMode j) + fiberTerm d (negMode j)) w.l 0 ≤
      ∑ j ∈ Finset.range (2 ^ M), U.getD j 0 := by
    rw [hl]
    have := balSum_le_of_shards (fun j => fiberTerm d (posMode j) + fiberTerm d (negMode j)) l₀
      (fun j => U.getD j 0) M 0 0 fun j hj => by simpa using (hs j hj).2
    simpa using this
  have hcheck : balCheck d w.l = true := by
    simp only [sideOk, Bool.and_eq_true] at hside
    simp only [balCheck, Bool.and_eq_true]
    exact ⟨hside, hA⟩
  have hbound : balBound d w.l ≤ w.B := by
    refine le_trans ?_ hB
    simp only [balBound]
    linarith
  simp only [biteOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨hc, hb⟩, hcheck⟩, hbound⟩, hnum⟩

end KAM.CertificateSharp.V2

end
