/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert

/-!
# Advice lookups by blocks

A product's `adviceLookup cfg.advice key = some (.packed …)` was proved by `rfl`: the elaborator
walks the book one entry at a time and reaches its maximum recursion depth past entry ~200
(measured: entry 966 of the `cfgLow` book fails, entry 203 passes). The books are chunks of 200
entries (`advLow.b0 ++ …`). Here a lookup skips whole chunks whose keys all differ from the key (a
Boolean check for the kernel) and finds the entry inside one chunk by a shallow `getElem?` (at most
199 cells) and a key comparison (kernel).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate

/-- A lookup skips a prefix of the book none of whose keys is the key. -/
theorem adviceLookup_skip_cseg (A B : AdviceBook) (k : ProductKey)
    (h : (A.all fun e => !(e.1 == k)) = true) : adviceLookup (A ++ B) k = adviceLookup B k := by
  have hn : A.find? (fun e => e.1 == k) = none := by
    rw [List.find?_eq_none]
    intro e he
    have := List.all_eq_true.mp h e he
    simpa using this
  simp [adviceLookup, List.find?_append, hn]

/-- A lookup at position `m` of a chunk: no earlier key of the chunk is the key, and the entry at
`m` has it. -/
theorem adviceLookup_at_cseg (A B : AdviceBook) (k : ProductKey) (m : ℕ) (k' : ProductKey)
    (a : ProductAdvice) (hpre : ((A.take m).all fun e => !(e.1 == k)) = true)
    (hm : A[m]? = some (k', a)) (hk : (k' == k) = true) : adviceLookup (A ++ B) k = some a := by
  have hA : A = A.take m ++ (k', a) :: A.drop (m + 1) := by
    have hlt : m < A.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hm
      exact absurd hm (by simp)
    rw [List.getElem?_eq_getElem hlt] at hm
    have he : A[m] = (k', a) := Option.some.inj hm
    conv_lhs => rw [← List.take_append_drop m A]
    rw [List.drop_eq_getElem_cons hlt, he]
  rw [hA, List.append_assoc, adviceLookup_skip_cseg _ _ k hpre]
  simp [adviceLookup, List.find?_cons, hk]

/-- The `cfgLow` book in its chunks (the seventh, `advLow.b6`, holds the SOS-square advice). -/
theorem lock_advLow_blocks :
    base.cfgLow.advice =
      advLow.b0 ++ (advLow.b1 ++ (advLow.b2 ++ (advLow.b3 ++ (advLow.b4 ++
        (advLow.b5 ++ advLow.b6))))) := by
  show advLow ++ advLow.b6 = _
  unfold advLow
  simp only [List.append_assoc]

/-- The `cfgFull` book in its chunks. -/
theorem lock_advFull_blocks :
    base.cfgFull.advice =
      advFull.b0 ++ (advFull.b1 ++ (advFull.b2 ++ (advFull.b3 ++ advFull.b4))) := by
  show advFull = _
  unfold advFull
  simp only [List.append_assoc]

end KAM.SpinOrbit.Data.LockN65
