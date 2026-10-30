/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Interface

/-!
# Balanced upward sums

`sumUp g L` rounds `Σ g x` upward as a balanced tree (`pairRounds`: 64 rounds of pairwise sums,
then a `foldr` of what remains). The kernel reduces such a sum at depth about `log₂` of the
length; a linear `foldr`/`foldl` accumulator over a term list of a few thousand entries exceeds
the kernel's reduction depth. Upward rounding depends on the order of the additions, so a
balanced sum is in general not equal to a linear one; consumers use the bound `sumUp_ge`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open CertArith

section Sums

variable {α : Type} [CertArith α]

/-- One round of pairwise upward sums: `[a, b, c, d, e] ↦ [a + b, c + d, e]`. -/
def sumPairsUp : List α → List α
  | a :: b :: rest => upAdd a b :: sumPairsUp rest
  | l => l

/-- `r` rounds of `sumPairsUp` (a list of length `≤ 2^r` collapses to at most one entry). -/
def pairRounds : ℕ → List α → List α
  | 0, l => l
  | r + 1, l => pairRounds r (sumPairsUp l)

/-- `Σ g x` rounded upward, summed as a balanced tree (64 rounds of pairwise sums, then a
`foldr` of what remains): the kernel evaluates nested sums of depth about `log₂` of the length,
never a long accumulator chain. -/
def sumUp {β : Type} (g : β → α) (L : List β) : α :=
  (pairRounds 64 (L.map g)).foldr upAdd (ofInt 0)

variable [LawfulCertArith α]

theorem sumPairsUp_ge : ∀ l : List α, (l.map val).sum ≤ ((sumPairsUp l).map val).sum
  | [] => le_rfl
  | [a] => le_rfl
  | a :: b :: rest => by
    have ih := sumPairsUp_ge rest
    have hu := LawfulCertArith.upAdd_ge a b
    simp only [sumPairsUp, List.map_cons, List.sum_cons]
    linarith

theorem pairRounds_ge : ∀ (r : ℕ) (l : List α),
    (l.map val).sum ≤ ((pairRounds r l).map val).sum
  | 0, _ => le_rfl
  | r + 1, l => (sumPairsUp_ge l).trans (pairRounds_ge r (sumPairsUp l))

theorem foldr_upAdd_ge : ∀ l : List α, (l.map val).sum ≤ val (l.foldr upAdd (ofInt 0))
  | [] => by simp [LawfulCertArith.val_ofInt]
  | a :: l => by
    have ih := foldr_upAdd_ge l
    have hu := LawfulCertArith.upAdd_ge a (l.foldr upAdd (ofInt 0))
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    linarith

theorem sumUp_ge {β : Type} (g : β → α) (L : List β) :
    (L.map fun x => val (g x)).sum ≤ val (sumUp g L) := by
  have h := (pairRounds_ge 64 (L.map g)).trans (foldr_upAdd_ge _)
  rw [List.map_map] at h
  exact h

end Sums

end KAM.Certificate
