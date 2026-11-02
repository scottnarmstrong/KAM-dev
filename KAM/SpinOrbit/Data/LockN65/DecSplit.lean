/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.MulPacked

/-!
# Decoding a packed product in slot pieces (LOCK-DATA)

The decode of a packed product (`dyadicTerms … adv.targetTerms = some T`) is one kernel evaluation
of the whole overlap-added target; for the largest lock products that needs more than the
per-theorem memory budget. This module cuts it at slot boundaries:

* `pieceAt f l a b`: the `filterMap` of `(index, entry)` pairs over the slots `[a, b)`;
* `filterMap_zip_range_eq_flatten`: the whole `filterMap` over `(List.range n).zip l` is the
  concatenation of its pieces along a monotone list of cuts from `0` to `n = l.length`;
* `dyadicTerms_flatten`: `dyadicTerms` of a concatenation, from the pieces' decodes;
* `dyadicTerms_targetTerms_of_pieces`: the decode of `adv.targetTerms` from the decodes of its
  pieces (each piece its own kernel theorem).

Nothing here is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith

section Pieces

variable {β γ : Type}

/-- The `filterMap` of the indexed entries of `l` over the slots `[a, b)`. -/
def pieceAt (f : ℕ × β → Option γ) (l : List β) (a b : ℕ) : List γ :=
  ((List.range' a (b - a)).zip ((l.drop a).take (b - a))).filterMap f

theorem pieceAt_split (f : ℕ × β → Option γ) (l : List β) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ l.length) : pieceAt f l a c = pieceAt f l a b ++ pieceAt f l b c := by
  have hca : c - a = (b - a) + (c - b) := by omega
  have hr : List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
    rw [hca, ← List.range'_append_1]
    congr 2
    omega
  have ht : (l.drop a).take (c - a) = (l.drop a).take (b - a) ++ (l.drop b).take (c - b) := by
    rw [hca, List.take_add, List.drop_drop]
    congr 3
    omega
  have hlen : (List.range' a (b - a)).length = ((l.drop a).take (b - a)).length := by
    simp only [List.length_range', List.length_take, List.length_drop]
    omega
  unfold pieceAt
  rw [hr, ht, List.zip_append hlen, List.filterMap_append]

/-- A list of cuts is monotone from `a`. -/
def monoFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: rest => decide (a ≤ b) && monoFrom b rest

/-- Consecutive pairs of a list of cuts. -/
def cutPairs : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: cutPairs (b :: rest)
  | _ => []

theorem le_getLast_of_monoFrom : ∀ (b : ℕ) (rest : List ℕ), monoFrom b rest = true →
    b ≤ (b :: rest).getLast (List.cons_ne_nil _ _)
  | b, [], _ => by simp
  | b, c :: rest, h => by
    simp only [monoFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    exact h.1.trans (le_getLast_of_monoFrom c rest h.2)

theorem pieceAt_eq_flatten (f : ℕ × β → Option γ) (l : List β) :
    ∀ (a : ℕ) (rest : List ℕ), monoFrom a rest = true →
      ((a :: rest).getLast (List.cons_ne_nil _ _)) ≤ l.length →
      pieceAt f l a ((a :: rest).getLast (List.cons_ne_nil _ _)) =
        ((cutPairs (a :: rest)).map fun p => pieceAt f l p.1 p.2).flatten
  | a, [], _, _ => by simp [pieceAt, cutPairs]
  | a, b :: rest, hch, hl => by
    simp only [monoFrom, Bool.and_eq_true, decide_eq_true_eq] at hch
    have hb := le_getLast_of_monoFrom b rest hch.2
    rw [List.getLast_cons (List.cons_ne_nil _ _)] at hl ⊢
    rw [pieceAt_split f l hch.1 hb hl, pieceAt_eq_flatten f l b rest hch.2 hl]
    simp [cutPairs]

theorem filterMap_zip_range_eq_flatten (f : ℕ × β → Option γ) (l : List β) (rest : List ℕ)
    (hch : monoFrom 0 rest = true)
    (hl : ((0 :: rest).getLast (List.cons_ne_nil _ _)) = l.length) :
    ((List.range l.length).zip l).filterMap f =
      ((cutPairs (0 :: rest)).map fun p => pieceAt f l p.1 p.2).flatten := by
  rw [← pieceAt_eq_flatten f l 0 rest hch hl.le, hl]
  simp [pieceAt, List.range_eq_range']

end Pieces

section Decode

variable {α : Type} [CertArith α]

theorem dyadicTerms_append (P2 sc : ℕ) (place : α → CC α) {x y : List (CertKey × ℤ)}
    {X Y : List (CertKey × CC α)} (hx : dyadicTerms P2 sc place x = some X)
    (hy : dyadicTerms P2 sc place y = some Y) :
    dyadicTerms P2 sc place (x ++ y) = some (X ++ Y) := by
  unfold dyadicTerms at hx hy ⊢
  split at hx <;> split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hx hy
  rename_i h1 h2
  have hxy : ((x ++ y).all fun t => (ofDyadicScaled P2 sc t.2 : Option α).isSome) = true := by
    rw [List.all_append, h1, h2]
    rfl
  simp only [hxy, ↓reduceIte, List.map_append, hx, hy]

theorem dyadicTerms_flatten (P2 sc : ℕ) (place : α → CC α) :
    ∀ {xs : List (List (CertKey × ℤ))} {Xs : List (List (CertKey × CC α))},
      List.Forall₂ (fun x X => dyadicTerms P2 sc place x = some X) xs Xs →
      dyadicTerms P2 sc place xs.flatten = some Xs.flatten
  | [], [], .nil => by simp [dyadicTerms]
  | _ :: _, _ :: _, .cons h hs => by
    rw [List.flatten_cons, List.flatten_cons]
    exact dyadicTerms_append P2 sc place h (dyadicTerms_flatten P2 sc place hs)

/-- The decode of a packed product's target from the decodes of its slot pieces along the cuts
`0 :: rest` (ending at `prodLen`). -/
theorem dyadicTerms_targetTerms_of_pieces (P2 sc : ℕ) (place : α → CC α) (adv : PackedAdvice)
    (rest : List ℕ) (hch : monoFrom 0 rest = true)
    (hl : ((0 :: rest).getLast (List.cons_ne_nil _ _)) = adv.prodLen)
    {Xs : List (List (CertKey × CC α))}
    (h : List.Forall₂ (fun p X => dyadicTerms P2 sc place
      (pieceAt adv.targetEntry adv.combined p.1 p.2) = some X) (cutPairs (0 :: rest)) Xs) :
    dyadicTerms P2 sc place adv.targetTerms = some Xs.flatten := by
  have hlen := adv.combined_length
  unfold PackedAdvice.targetTerms
  rw [← hlen, filterMap_zip_range_eq_flatten _ _ rest hch (hl.trans hlen.symm)]
  apply dyadicTerms_flatten
  rw [List.forall₂_map_left_iff]
  exact h

omit [CertArith α] in
/-- The first component of the target pair, as a rewrite (generic, so no evaluation of the
remainder bound or of the target is needed to use it). -/
theorem fst_targetPair (adv : PackedAdvice) (rb : α) : (adv.targetTerms, rb).1 = adv.targetTerms :=
  rfl

end Decode

end KAM.SpinOrbit.Data.LockN65
