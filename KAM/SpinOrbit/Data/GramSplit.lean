/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs

/-!
# Sharding the Gram check of a two-dimensional certificate (SO-DATA3)

`gramCheck` computes the Gram models, the two defect rows `gramDefectRows` and the final tests in
one evaluation, which is too large for a single kernel check on the lunar data. Here:

* `gramDefectRows_two`: the row list from its two entries, each a kernel computation of its own;
* `gramCheck_eq_of_rows`: `gramCheck` with the defect rows replaced by a given list, so that the
  checks consuming `gramCheck` (`checkGram`, `checkTorsion`, the frame majorants) can be
  evaluated with the rows as literals;
* `CertFixed.eq_of_m`: a fixed-point number from its mantissa.

Every statement is an equation between computable terms; nothing is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data

open KAM.Certificate CertArith

theorem CertFixed.eq_of_m {P : ℕ} {x : CertFixed P} {k : ℤ} (h : x.m = k) : x = ⟨k⟩ := by
  cases x
  simp_all

/-- The defect rows of a two-dimensional Gram check from their two entries. -/
theorem gramDefectRows_two {α : Type} [CertArith α] {B : List (List (CertPoly α))}
    {G : ModelMatrix α} {W : CertWeight} {cfg : ModelConfig α} {pe : PiEnclosure α} {x₀ x₁ : α}
    (h₀ : (gramDefectRows 2 B G W cfg pe).getD 0 (ofInt 0) = x₀)
    (h₁ : (gramDefectRows 2 B G W cfg pe).getD 1 (ofInt 0) = x₁) :
    gramDefectRows 2 B G W cfg pe = [x₀, x₁] := by
  rw [← h₀, ← h₁]
  simp [gramDefectRows, List.ofFn_succ]

/-- `gramCheck` with its defect rows given. -/
theorem gramCheck_eq_of_rows {n : ℕ} {α : Type} [CertArith α] {K : CertEmbedding α}
    {B : List (List (CertPoly α))} {W : CertWeight} {cfg : ModelConfig α} {pe : PiEnclosure α}
    {σBμ : ℚ} {d : List α} (hs : gramInvShapeOk n B = true)
    (hd : gramDefectRows n B (gramModels n K W cfg pe) W cfg pe = d) :
    gramCheck n K B W cfg pe σBμ =
      if gramBoundsOk d (gramInvRows n B W) (maxCandidate d) (maxCandidate (gramInvRows n B W))
          σBμ then
        some (maxCandidate d, maxCandidate (gramInvRows n B W))
      else none := by
  simp only [gramCheck, hs, hd, ite_true]

end KAM.SpinOrbit.Data
