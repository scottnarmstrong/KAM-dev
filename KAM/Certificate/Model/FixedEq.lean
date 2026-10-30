/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Model.Terms
public import KAM.Certificate.Arith.Fixed

/-!
# Balanced sums are exact on the fixed-point backend

On `CertFixed P`, `upAdd` is exact integer addition, so the balanced `sumUp` has the same value
as a linear `foldr` in any order. In particular the balanced `CertPoly.weightedNormUp` equals its
former linear definition (`CertPoly.weightedNormUp_fixed_eq`), so the value computed by the
checker on the fixed backend is unchanged.
-/

@[expose] public section

namespace KAM.Certificate

open CertArith

variable {P : ℕ}

theorem CertFixed.eq_of_m {a b : CertFixed P} (h : a.m = b.m) : a = b := by
  cases a; cases b; cases h; rfl

theorem sumPairsUp_fixed_m : ∀ l : List (CertFixed P),
    ((sumPairsUp l).map CertFixed.m).sum = (l.map CertFixed.m).sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [sumPairsUp, List.map_cons, List.sum_cons, sumPairsUp_fixed_m rest]
    change (a.m + b.m) + _ = _
    ring

theorem pairRounds_fixed_m : ∀ (r : ℕ) (l : List (CertFixed P)),
    ((pairRounds r l).map CertFixed.m).sum = (l.map CertFixed.m).sum
  | 0, _ => rfl
  | r + 1, l => (pairRounds_fixed_m r (sumPairsUp l)).trans (sumPairsUp_fixed_m l)

theorem foldr_upAdd_fixed_m : ∀ l : List (CertFixed P),
    (l.foldr upAdd (ofInt 0)).m = (l.map CertFixed.m).sum
  | [] => by simp [CertArith.ofInt, CertFixed.ulpDen]
  | a :: l => by
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ← foldr_upAdd_fixed_m l]
    rfl

/-- On the fixed backend the balanced upward sum is the exact integer sum. -/
theorem sumUp_fixed_m {β : Type} (g : β → CertFixed P) (L : List β) :
    (sumUp g L).m = (L.map fun x => (g x).m).sum := by
  unfold sumUp
  rw [foldr_upAdd_fixed_m, pairRounds_fixed_m, List.map_map]
  rfl

/-- **Value preservation**: on the fixed backend the balanced `weightedNormUp` equals its former
linear definition (a `foldr` of `upAdd` over the terms). -/
theorem CertPoly.weightedNormUp_fixed_eq (W : CertWeight) (Q : CertPoly (CertFixed P)) :
    Q.weightedNormUp W = Q.terms.foldr (fun (t : CertKey × CC (CertFixed P)) acc =>
      upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0) := by
  have h : ∀ L : List (CertKey × CC (CertFixed P)),
      (L.foldr (fun (t : CertKey × CC (CertFixed P)) acc =>
      upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0)).m =
      (L.map fun (t : CertKey × CC (CertFixed P)) => (upMul t.2.normUp
        (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum)) : CertFixed P).m).sum := by
    intro L
    induction L with
    | nil => simp [CertArith.ofInt, CertFixed.ulpDen]
    | cons t L ih =>
      rw [List.foldr_cons, List.map_cons, List.sum_cons, ← ih]
      rfl
  have e : (Q.weightedNormUp W).m = (Q.terms.foldr (fun (t : CertKey × CC (CertFixed P)) acc =>
      upAdd (upMul t.2.normUp (ofRatUp (W.w ^ (t.1.map Int.natAbs).sum))) acc) (ofInt 0)).m := by
    rw [h]
    exact sumUp_fixed_m _ _
  exact CertFixed.eq_of_m e

end KAM.Certificate
