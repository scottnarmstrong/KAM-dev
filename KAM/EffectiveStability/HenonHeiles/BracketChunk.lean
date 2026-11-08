/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.ChunkMerge

/-!
# Seed-chunked majorants of brackets over `ℚ(√2)` (track B, B3-CERT)

`cartSupBound (cartBracketW w P Q)` is additive over a splitting `P = P₁ ++ P₂` of the first
argument (the majorant is a sum over the monomials of the unmerged bracket, which distributes over
the seeds `P`). `supBoundBr_chunk` lets the kernel evaluate the majorant of a bracket with a huge
unmerged expansion seed-chunk by seed-chunk, each chunk touching only its own seeds.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

theorem supBound_append' (P Q : CartPolyK QSqrt2) (r t : List ℚ) :
    cartSupBound (P ++ Q) r t = cartSupBound P r t + cartSupBound Q r t := by
  simp [cartSupBound, List.map_append, List.sum_append]

theorem supBound_neg' (P : CartPolyK QSqrt2) (r t : List ℚ) :
    cartSupBound (cartNeg P) r t = cartSupBound P r t := by
  induction P with
  | nil => simp [cartNeg, cartSupBound]
  | cons m P ih =>
    simp only [cartNeg, cartSupBound, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [cartMonoBound, CertCoeff.absUB, QSqrt2.absUB, QSqrt2.neg_a,
      QSqrt2.neg_b, abs_neg]

theorem supBound_flatMap {α : Type} (L : List α) (g : α → CartPolyK QSqrt2) (r t : List ℚ) :
    cartSupBound (L.flatMap g) r t = (L.map fun x => cartSupBound (g x) r t).sum := by
  induction L with
  | nil => simp [cartSupBound]
  | cons x L ih => simp [List.flatMap_cons, supBound_append', ih]

theorem supBound_mul_append (A1 A2 B : CartPolyK QSqrt2) (r t : List ℚ) :
    cartSupBound (cartMul (A1 ++ A2) B) r t =
      cartSupBound (cartMul A1 B) r t + cartSupBound (cartMul A2 B) r t := by
  simp only [cartMul, List.flatMap_append, supBound_append']

theorem supBound_term_append (i : ℕ) (P1 P2 Q : CartPolyK QSqrt2) (r t : List ℚ) :
    cartSupBound (cartSub (cartMul (cartDq i (P1 ++ P2)) (cartDp i Q))
        (cartMul (cartDp i (P1 ++ P2)) (cartDq i Q))) r t =
      cartSupBound (cartSub (cartMul (cartDq i P1) (cartDp i Q))
        (cartMul (cartDp i P1) (cartDq i Q))) r t +
      cartSupBound (cartSub (cartMul (cartDq i P2) (cartDp i Q))
        (cartMul (cartDp i P2) (cartDq i Q))) r t := by
  simp only [cartSub, cartAdd, supBound_append', supBound_neg', cartDq, cartDp,
    List.flatMap_append, supBound_mul_append]
  ring

theorem supBound_bracketW_append (w : ℕ) (P1 P2 Q : CartPolyK QSqrt2) (r t : List ℚ) :
    cartSupBound (cartBracketW w (P1 ++ P2) Q) r t =
      cartSupBound (cartBracketW w P1 Q) r t + cartSupBound (cartBracketW w P2 Q) r t := by
  simp only [cartBracketW, supBound_flatMap, supBound_term_append, List.sum_map_add]

/-- Seed-chunked bracket majorant: the suffix `P.drop s` of seeds is its first `n` seeds plus the
suffix `P.drop e` (`e = s + n`). -/
theorem supBoundBr_chunk (P Q : CartPolyK QSqrt2) (w s n e : ℕ) (he : s + n = e) (r t : List ℚ)
    (B a : ℚ) (h : cartSupBound (cartBracketW w (P.drop e) Q) r t = B)
    (hc : cartSupBound (cartBracketW w ((P.drop s).take n) Q) r t = a) :
    cartSupBound (cartBracketW w (P.drop s) Q) r t = a + B := by
  conv_lhs => rw [← List.take_append_drop n (P.drop s)]
  rw [supBound_bracketW_append, List.drop_drop, he, h, hc]

end KAM.EffectiveStability.HenonHeiles

end
