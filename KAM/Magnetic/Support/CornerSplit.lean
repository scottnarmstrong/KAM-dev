/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Corner.SupBound

/-!
# The frame corner checks, one vertex at a time (MAG-SEAL)

Structural lemmas that let the frame checks (`checkFrameT`, `checkFrameN`) be proved from one
`decide +kernel` per row (or column) and vertex, each its own declaration, instead of one evaluation
of all rows and vertices (copied from `KAM.SpinOrbit.Data.LockN65.CornerSplit`).

As for the lunar lock, the single all-vertex evaluation of the magnetic frame checks did not finish
in 1,800 s at about 2.3 GB (lam, MAG-3): the kernel's per-declaration caches degrade superlinearly
with the number of big literals sharing a low limb
(`docs/explorations/lean-kernel-nat-literal-hash.md`).
Splitting the evaluation keeps each declaration small. Nothing is computed here: the lemmas only
reassemble the per-vertex facts.
-/

@[expose] public section

namespace KAM.Magnetic.Data

open KAM KAM.Certificate KAM.CertificateSharp CertArith

variable {α : Type} [CertArith α]

/-- The four vertices at `n = 2`, in the order `signLists` lists them. -/
theorem signLists_two :
    signLists 2 = [[true, true], [false, true], [true, false], [false, false]] := rfl

/-- A row-sum corner check at `n = 2` from its four vertices. -/
theorem rowCornerLeq_two {W : CertWeight} {wlo : ℚ} {ms : List (CertModel α)} {b : α}
    (h₁ : ble (rowCornerUp W wlo [true, true] ms) b = true)
    (h₂ : ble (rowCornerUp W wlo [false, true] ms) b = true)
    (h₃ : ble (rowCornerUp W wlo [true, false] ms) b = true)
    (h₄ : ble (rowCornerUp W wlo [false, false] ms) b = true) :
    rowCornerLeq W wlo 2 ms b = true := by
  simp only [rowCornerLeq, signLists_two, List.all_cons, List.all_nil, h₁, h₂, h₃, h₄,
    Bool.and_self]

/-- `(List.finRange 2).all p` from `p 0` and `p 1`. -/
theorem all_finRange_two {p : Fin 2 → Bool} (h₀ : p 0 = true) (h₁ : p 1 = true) :
    (List.finRange 2).all p = true := by
  rw [List.all_eq_true]
  intro i _
  fin_cases i
  · exact h₀
  · exact h₁

/-- `(List.finRange (2 + 2)).all p` from `p 0`, …, `p 3`. -/
theorem all_finRange_four {p : Fin (2 + 2) → Bool} (h₀ : p 0 = true) (h₁ : p 1 = true)
    (h₂ : p 2 = true) (h₃ : p 3 = true) : (List.finRange (2 + 2)).all p = true := by
  rw [List.all_eq_true]
  intro i _
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃

/-- `a && b` from both. -/
theorem and_eq_true_of {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

end KAM.Magnetic.Data
