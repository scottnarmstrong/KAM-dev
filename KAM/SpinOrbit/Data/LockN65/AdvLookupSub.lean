/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.ComposeModels

/-!
# Advice lookups in a witness's sub-book (lock-owned)

A witness product (`cfg.forWitness s i`) looks its advice up in `subAdvice s i cfg.advice`
under its own key `s :: rest`. Matching that against a lookup in the whole book left the
elaborator to evaluate both books entry by entry, and it reached its maximum recursion depth at
chunk entries 158/159/178/179 (lam run, M558/M559/M578/M579).
`adviceLookup_forWitness_cseg` (through `adviceLookup_subAdvice_cseg`) turns the sub-book
lookup into a lookup of `s :: i :: rest` in the whole book, which then goes by chunks
(`AdvLookup.lean`). Nothing is assumed about the data.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate

/-- A lookup in the sub-book of witness `i` at site `s` is the lookup of the full key in the
book. -/
theorem adviceLookup_subAdvice_cseg (s i : ℕ) (rest : List ℕ) :
    ∀ book : AdviceBook,
      adviceLookup (subAdvice s i book) (s :: rest) = adviceLookup book (s :: i :: rest)
  | [] => rfl
  | (key, a) :: book => by
    have ih := adviceLookup_subAdvice_cseg s i rest book
    unfold adviceLookup subAdvice at ih ⊢
    rcases key with _ | ⟨x, _ | ⟨y, r⟩⟩
    · simpa [List.find?_cons] using ih
    · simpa [List.find?_cons] using ih
    · by_cases h : x = s ∧ y = i
      · obtain ⟨rfl, rfl⟩ := h
        by_cases hr : r = rest
        · subst hr
          simp
        · simpa [List.filterMap_cons, List.find?_cons, hr] using ih
      · rw [List.filterMap_cons]
        simp only [h, ite_false]
        rw [List.find?_cons_of_neg (by
          simp only [List.cons.injEq, beq_iff_eq, not_and]
          intro hx hy
          exact absurd ⟨hx, hy⟩ h)]
        exact ih

/-- The same for a witness configuration: stated on `(cfg.forWitness s i).advice` itself, so
a product's lookup unifies without unfolding `subAdvice` (lazy delta would evaluate the
book). -/
theorem adviceLookup_forWitness_cseg {α : Type} (cfg : ModelConfig α) (s i : ℕ)
    (rest : List ℕ) :
    adviceLookup (cfg.forWitness s i).advice (s :: rest) =
      adviceLookup cfg.advice (s :: i :: rest) :=
  adviceLookup_subAdvice_cseg s i rest cfg.advice

end KAM.SpinOrbit.Data.LockN65
