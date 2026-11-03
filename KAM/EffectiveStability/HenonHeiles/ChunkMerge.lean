/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Basic
public import KAM.EffectiveStability.Poly.Bound
public import KAM.EffectiveStability.Poly.Bracket

/-!
# Chunked kernel verification of `cartEqCheck` and `cartSupBound` (track B, B3-CERT)

`cartEqCheck P Q` merges the unmerged list `cartSub P Q` with a right fold, whose kernel
evaluation recurses to the depth of the list (the kernel stack overflows beyond a few thousand
monomials; the unmerged Lie sums of the Hénon–Heiles certificate have up to ~10⁴).
`chunk_step` replays the same fold in chunks of `n` monomials onto claimed intermediate
accumulators (untrusted data), each chunk being a separate small kernel computation, so that no
kernel recursion is deeper than a chunk and the kernel caches stay small;
`cartEqCheck_of_merge` turns the resulting merge identity into `cartEqCheck P Q = true`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

variable {K : Type} [CertCoeff K]

/-- One chunk of the replay: if the suffix `Y.drop e` merges to `B` and the chunk
`Y.take n` of the suffix `Y.drop s` merges onto `B` to `A`, then `Y.drop s` merges to `A`
(`e = s + n`). -/
theorem chunk_step (Y : List (CartMonoK K)) (s n e : ℕ) (he : s + n = e)
    (B A : List (CartMonoK K)) (h : (Y.drop e).foldr cartInsertMono [] = B)
    (hc : ((Y.drop s).take n).foldr cartInsertMono B = A) :
    (Y.drop s).foldr cartInsertMono [] = A := by
  conv_lhs => rw [← List.take_append_drop n (Y.drop s)]
  rw [List.foldr_append, List.drop_drop, he, h]
  exact hc

/-- The chunked identity check: if the merge of `cartSub P Q` (after trimming) is `A` and `A`
has no nonzero coefficient, then `cartEqCheck P Q = true`. -/
theorem cartEqCheck_of_merge {P Q : CartPolyK K} {A : List (CartMonoK K)}
    (h : ((cartSub P Q).map CartMonoK.cartMonoTrim).foldr cartInsertMono [] = A)
    (h0 : (A.filter fun m => decide (m.c ≠ 0)).isEmpty = true) : cartEqCheck P Q = true := by
  simp only [cartEqCheck, cartNormalize, cartMerge]
  rw [h]
  exact h0

/-- Chunked `cartSupBound`: the bound of the suffix `Z.drop s` is the bound of its first `n`
monomials plus the bound of the suffix `Z.drop e` (`e = s + n`). -/
theorem supBound_chunk (Z : CartPolyK K) (s n e : ℕ) (he : s + n = e) (r t : List ℚ)
    (B a : ℚ) (h : cartSupBound (Z.drop e) r t = B)
    (hc : cartSupBound ((Z.drop s).take n) r t = a) : cartSupBound (Z.drop s) r t = a + B := by
  unfold cartSupBound at *
  conv_lhs => rw [← List.take_append_drop n (Z.drop s)]
  rw [List.map_append, List.sum_append, List.drop_drop, he, h, hc]

omit [CertCoeff K] in
/-- Chunked `cartWidth` (the recursion of `cartWidth` is as deep as the list). -/
theorem width_chunk (Z : CartPolyK K) (s n e : ℕ) (he : s + n = e) (B a : ℕ)
    (h : cartWidth (Z.drop e) = B) (hc : cartWidth ((Z.drop s).take n) = a) :
    cartWidth (Z.drop s) = max a B := by
  have key : ∀ P Q : CartPolyK K, cartWidth (P ++ Q) = max (cartWidth P) (cartWidth Q) := by
    intro P Q
    induction P with
    | nil => simp [cartWidth]
    | cons m P ih => simp only [List.cons_append, cartWidth, ih, max_assoc]
  conv_lhs => rw [← List.take_append_drop n (Z.drop s)]
  rw [key, List.drop_drop, he, h, hc]

/-- The bracket with an explicitly given index range (equal to `cartBracket` when the range is
the width of the first argument, which the kernel computes by `width_chunk`). -/
def cartBracketW (w : ℕ) (P Q : CartPolyK K) : CartPolyK K :=
  (List.range w).flatMap fun i =>
    cartSub (cartMul (cartDq i P) (cartDp i Q)) (cartMul (cartDp i P) (cartDq i Q))

theorem cartBracket_width {P : CartPolyK K} {w : ℕ} (Q : CartPolyK K) (h : cartWidth P = w) :
    cartBracket P Q = cartBracketW w P Q := by
  subst h
  rfl

end KAM.EffectiveStability.HenonHeiles

end
