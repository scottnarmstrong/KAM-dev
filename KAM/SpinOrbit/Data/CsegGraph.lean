/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.CsegSupport
public import KAM.Certificate.Positivity

/-!
# The graph check by row chunks (SO-DATA3)

`checkRealLowerBound` forms the SOS square `g g*` by the direct product (`[7]`, forced
`.direct`): one `directItems` of all `|g|²` term pairs, too large for one kernel check on the
lunar witnesses. The
landed `directItems` merges its rows as a balanced tree (`mergeRowsTree`, pairing positionally), so
`k` merge levels over a row list whose chunks have `2^k` rows are the chunk-wise levels
(`levelNCseg_flatten`): each chunk is one kernel computation, and the rest of the tree runs on the
chunk results as literals. `realLowerModel_eq_of_sq_cseg` and `adviceLookup_append_cseg` put the
memoized square back. Equations between computable terms; nothing is assumed about the data.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data

open KAM.Certificate CertArith

/-! ### The direct product by row chunks (the SOS square `g g*` of the graph check) -/

section Rows

variable {α : Type} [CertArith α]

/-- `k` levels of the landed `mergeRowsLevel`. -/
def levelNCseg : ℕ → List (List (ErrTerm α)) → List (List (ErrTerm α))
  | 0, rows => rows
  | k + 1, rows => levelNCseg k (mergeRowsLevel rows)

theorem levelNCseg_nil (k : ℕ) : levelNCseg (α := α) k [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [levelNCseg]; exact ih

theorem mergeRowsTree_succ_cseg (f : ℕ) (rows : List (List (ErrTerm α))) :
    mergeRowsTree (f + 1) rows = mergeRowsTree f (mergeRowsLevel rows) := by
  match rows with
  | [] => simp [mergeRowsTree, mergeRowsLevel]
  | [a] => simp [mergeRowsTree, mergeRowsLevel]
  | a :: b :: r => rfl

theorem mergeRowsTree_add_cseg (f k : ℕ) (rows : List (List (ErrTerm α))) :
    mergeRowsTree (f + k) rows = mergeRowsTree f (levelNCseg k rows) := by
  induction k generalizing rows with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, mergeRowsTree_succ_cseg, ih]; rfl

theorem mergeRowsLevel_append_cseg :
    ∀ (A B : List (List (ErrTerm α))), A.length % 2 = 0 →
      mergeRowsLevel (A ++ B) = mergeRowsLevel A ++ mergeRowsLevel B
  | [], B, _ => by simp [mergeRowsLevel]
  | [_], _, h => absurd h (by simp)
  | a :: b :: r, B, h => by
    simp only [List.cons_append, mergeRowsLevel]
    rw [mergeRowsLevel_append_cseg r B (by simp only [List.length_cons] at h; omega)]

theorem length_mergeRowsLevel_cseg :
    ∀ (A : List (List (ErrTerm α))) (m : ℕ), A.length = 2 * m → (mergeRowsLevel A).length = m
  | [], m, h => by simp at h; simp [mergeRowsLevel]; omega
  | [_], _, h => by simp at h; omega
  | a :: b :: r, m, h => by
    simp only [mergeRowsLevel, List.length_cons] at h ⊢
    rw [length_mergeRowsLevel_cseg r (m - 1) (by omega)]
    omega

theorem levelNCseg_append (k : ℕ) :
    ∀ (A B : List (List (ErrTerm α))), A.length = 2 ^ k →
      levelNCseg k (A ++ B) = levelNCseg k A ++ levelNCseg k B := by
  induction k with
  | zero => intro A B _; rfl
  | succ k ih =>
    intro A B h
    simp only [levelNCseg]
    rw [mergeRowsLevel_append_cseg A B (by rw [h, pow_succ]; omega)]
    exact ih _ _ (length_mergeRowsLevel_cseg A _ (by rw [h, pow_succ, mul_comm]))

/-- `k` merge levels over a chunked row list: chunk by chunk, when every chunk but the last has
`2^k` rows. -/
theorem levelNCseg_flatten (k : ℕ) (F : (CertKey × CC α) → List (ErrTerm α)) :
    ∀ (L : List (List (CertKey × CC α))),
      (L.dropLast.all fun c => c.length == 2 ^ k) = true →
      levelNCseg k ((L.flatten).map F) = (L.map fun c => levelNCseg k (c.map F)).flatten
  | [], _ => by simp [levelNCseg_nil]
  | [c], _ => by simp
  | c :: d :: r, h => by
    simp only [List.dropLast_cons₂, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.flatten_cons, List.map_append,
      levelNCseg_append k _ _ (by rw [List.length_map]; exact h.1),
      levelNCseg_flatten k F (d :: r) (by simpa using h.2)]
    simp

/-- The advice of a key appended at the end of a book that does not contain it. -/
theorem adviceLookup_append_cseg (book : AdviceBook) (k : ProductKey) (a : ProductAdvice)
    (h : (book.all fun e => !(e.1 == k)) = true) : adviceLookup (book ++ [(k, a)]) k = some a := by
  have hn : book.find? (fun e => e.1 == k) = none := by
    rw [List.find?_eq_none]
    intro e he
    have := List.all_eq_true.mp h e he
    simpa using this
  simp [adviceLookup, List.find?_append, hn]

/-- `realLowerModel` with its square `g g*` memoized. -/
theorem realLowerModel_eq_of_sq_cseg (W : CertWeight) (cfg : ModelConfig α) (f : CertModel α)
    (m₀ : ℚ) (g : CertPoly α) {gg : CertModel α}
    (h : CertModel.mul W { cfg with advice := cfg.advice ++ [([7], ProductAdvice.direct)] } [7]
      ⟨0, g, ofInt 0⟩ ⟨0, g.conjSorted, ofInt 0⟩ = gg) :
    CertModel.realLowerModel W cfg f m₀ g =
      CertModel.add W (CertModel.add W (CertModel.add W f f.starModel)
        (CertModel.mul W { cfg with advice := cfg.advice ++ [([7], ProductAdvice.direct)] } [7] gg
          (CertModel.ofConst g.keyLen (ofInt (-2)) (ofInt 0))))
        (CertModel.ofConst (if f.poly.terms.isEmpty then g.keyLen else f.poly.keyLen)
          (ofRatUp (-2 * m₀)) (upAdd (ofRatUp (-2 * m₀)) (neg (ofRatDown (-2 * m₀))))) := by
  simp only [CertModel.realLowerModel, h]


end Rows

section Lit

/-- A literal error term `([k₀, k₁], re + i im, err)` over `CertFixed P` (mantissas). -/
def etF (P : ℕ) (k₀ k₁ re im e : ℤ) : ErrTerm (CertFixed P) := ([k₀, k₁], ⟨⟨re⟩, ⟨im⟩⟩, ⟨e⟩)

variable {β : Type} [DecidableEq β]

/-- Tail-recursive equality of error-term lists. -/
def errTermsBeqCseg : List (ErrTerm β) → List (ErrTerm β) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    keyBeq a.1 b.1 && ccBeq a.2.1 b.2.1 && decide (a.2.2 = b.2.2) && errTermsBeqCseg as bs
  | _, _ => false

theorem eq_of_errTermsBeqCseg :
    ∀ {l l' : List (ErrTerm β)}, errTermsBeqCseg l l' = true → l = l'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [errTermsBeqCseg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hk, hc⟩, he⟩, hr⟩ := h
    rw [eq_of_errTermsBeqCseg hr, Prod.ext (eq_of_keyBeq hk) (Prod.ext (eq_of_ccBeq hc) he)]
  | [], _ :: _, h => by simp [errTermsBeqCseg] at h
  | _ :: _, [], h => by simp [errTermsBeqCseg] at h

/-- A row list equal to the singleton `[L]`. -/
theorem eq_singleton_of_beq_cseg {rows : List (List (ErrTerm β))} {L : List (ErrTerm β)}
    (h : (rows.map fun l => errTermsBeqCseg l L) = [true]) : rows = [L] := by
  match rows, h with
  | [], h => simp at h
  | [r], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [eq_of_errTermsBeqCseg h]
  | _ :: _ :: _, h => simp at h

end Lit

end KAM.SpinOrbit.Data
