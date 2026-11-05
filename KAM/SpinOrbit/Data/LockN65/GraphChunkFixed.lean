/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.GraphChunk
public import KAM.Certificate.Arith.Fixed

/-!
# Zero error radii on the fixed-point backend (lock-owned)

On `CertFixed P` the rounding error of an addition is `0` (`addErr _ _ = ⟨0⟩`), so a merge of
error-free term lists is error-free, and the error radius of an error-free list is `0`:
`errRadius_eq_zero`, `mergeErrTerms_errFree`, `toErrTerms_errFree`. The graph check's merged models
(SOS option (a)) then need no kernel run for these radii.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM.Certificate CertArith CertFixed

variable {P : ℕ}

/-- Every error of the list is zero. -/
def ErrFree (L : List (ErrTerm (CertFixed P))) : Prop := ∀ t ∈ L, t.2.2 = ⟨0⟩

theorem ofInt_zero_fixed : (ofInt 0 : CertFixed P) = ⟨0⟩ := by
  show (⟨0 * ulpDen P⟩ : CertFixed P) = ⟨0⟩
  simp

theorem weightTermUp_zero_fixed (W : CertWeight) (k : CertKey) :
    weightTermUp W k (⟨0⟩ : CertFixed P) = ⟨0⟩ := by
  show (⟨cdiv ((0 : ℤ).natAbs * (ofRatUp (W.w ^ keyDeg k) : CertFixed P).m) (ulpDen P)⟩ :
    CertFixed P) = ⟨0⟩
  simp [cdiv]

theorem sumPairsUp_zero_fixed :
    ∀ L : List (CertFixed P), (∀ x ∈ L, x = ⟨0⟩) → ∀ y ∈ sumPairsUp L, y = ⟨0⟩
  | [], _ => by simp [sumPairsUp]
  | [a], h => by simpa [sumPairsUp] using h
  | a :: b :: r, h => by
    intro y hy
    simp only [sumPairsUp, List.mem_cons] at hy
    rcases hy with hy | hy
    · subst hy
      have ha := h a (by simp)
      have hb := h b (by simp)
      subst ha hb
      rfl
    · exact sumPairsUp_zero_fixed r (fun x hx => h x (by simp [hx])) y hy

theorem pairRounds_zero_fixed :
    ∀ (r : ℕ) (L : List (CertFixed P)), (∀ x ∈ L, x = ⟨0⟩) → ∀ y ∈ pairRounds r L, y = ⟨0⟩
  | 0, _, h => h
  | r + 1, L, h => pairRounds_zero_fixed r _ (sumPairsUp_zero_fixed L h)

theorem foldr_upAdd_zero_fixed :
    ∀ L : List (CertFixed P), (∀ x ∈ L, x = ⟨0⟩) → L.foldr upAdd (ofInt 0) = ⟨0⟩
  | [], _ => ofInt_zero_fixed
  | a :: L, h => by
    rw [List.foldr_cons, foldr_upAdd_zero_fixed L (fun x hx => h x (by simp [hx])),
      h a (by simp)]
    rfl

theorem errRadius_eq_zero (W : CertWeight) (L : List (ErrTerm (CertFixed P)))
    (h : ErrFree L) : errRadius W L = ⟨0⟩ := by
  unfold errRadius sumUp
  apply foldr_upAdd_zero_fixed
  apply pairRounds_zero_fixed
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  rw [h t ht]
  exact weightTermUp_zero_fixed W t.1

theorem toErrTerms_errFree (Q : CertPoly (CertFixed P)) : ErrFree Q.toErrTerms := by
  intro t ht
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 ht
  exact ofInt_zero_fixed

theorem mergeErrPair_errFree (x y : ErrTerm (CertFixed P)) (hx : x.2.2 = ⟨0⟩)
    (hy : y.2.2 = ⟨0⟩) : (mergeErrPair x y).2.2 = ⟨0⟩ := by
  obtain ⟨k, c, e⟩ := x
  obtain ⟨l, d, f⟩ := y
  simp only at hx hy
  subst hx hy
  rfl

theorem mergeErrTerms_errFree :
    ∀ (A B : List (ErrTerm (CertFixed P))), ErrFree A → ErrFree B → ErrFree (mergeErrTerms A B)
  | [], B, _, hB => hB
  | x :: xs, B, hA, hB => by
    have hx : x.2.2 = ⟨0⟩ := hA x (by simp)
    have hxs : ErrFree xs := fun t ht => hA t (by simp [ht])
    rw [mergeErrTerms_cons]
    induction B with
    | nil =>
      intro t ht
      simp only [mergeErrInsert, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hx
      · exact hxs t ht
    | cons y ys ih =>
      have hy : y.2.2 = ⟨0⟩ := hB y (by simp)
      have hys : ErrFree ys := fun t ht => hB t (by simp [ht])
      intro t ht
      cases hc : keyCmp x.1 y.1 with
      | lt =>
        simp only [mergeErrInsert, hc, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hx
        · exact mergeErrTerms_errFree xs (y :: ys) hxs hB t ht
      | gt =>
        simp only [mergeErrInsert, hc, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hy
        · exact ih hys t ht
      | eq =>
        simp only [mergeErrInsert, hc, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact mergeErrPair_errFree x y hx hy
        · exact mergeErrTerms_errFree xs ys hxs hys t ht

end KAM.SpinOrbit.Data.LockN65
