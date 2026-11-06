/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Sparse integer polynomials as term lists (T2-CONF, N5a)

A sparse polynomial with keys in `K` is a list of terms `(k, c)`, `c : ℤ`, denoting `Σ c · m k` for
a key semantics `m : K → R` into a commutative ring (`levalBy`). Duplicate keys are allowed: every
operation is correct for arbitrary lists, and sortedness only matters for speed and for a canonical
form. The operations are kernel-friendly (structural recursion, integer arithmetic):

* `mergeWith lt comb p q`: the sorted merge, combining the values of equal keys
  (`sum_map_mergeWith`: preserves sum semantics additive in the values); `mergeAdd` adds integer
  coefficients (`levalBy_mergeAdd : levalBy m (mergeAdd lt p q) = levalBy m p + levalBy m q`);
* `scaleTerms c p`, `dropZeros`, with their semantics; `listBEq`, a kernel-friendly list equality.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

variable {K R : Type*}

/-- The value `Σ c · m k` of a term list under the key semantics `m`. -/
def levalBy [CommRing R] (m : K → R) (p : List (K × ℤ)) : R :=
  (p.map fun e => (e.2 : R) * m e.1).sum

section
variable [CommRing R] (m : K → R)

@[simp] theorem levalBy_nil : levalBy m ([] : List (K × ℤ)) = 0 := rfl

@[simp] theorem levalBy_cons (e : K × ℤ) (p : List (K × ℤ)) :
    levalBy m (e :: p) = (e.2 : R) * m e.1 + levalBy m p := by
  simp [levalBy]

@[simp] theorem levalBy_append (p q : List (K × ℤ)) :
    levalBy m (p ++ q) = levalBy m p + levalBy m q := by
  simp [levalBy]

end

section merge
variable {V : Type*} [DecidableEq K] (lt : K → K → Bool) (comb : V → V → V)

/-- The step of `mergeWith` with head `x`, tail `p` and the merge `f = mergeWith p` of the tail. -/
def mergeWithAux (x : K × V) (p : List (K × V)) (f : List (K × V) → List (K × V)) :
    List (K × V) → List (K × V)
  | [] => x :: p
  | y :: q =>
    if x.1 = y.1 then (x.1, comb x.2 y.2) :: f q
    else if lt x.1 y.1 then x :: f (y :: q) else y :: mergeWithAux x p f q

/-- The merge of two lists sorted by `lt`, combining the values of equal keys with `comb`. -/
def mergeWith : List (K × V) → List (K × V) → List (K × V)
  | [], q => q
  | x :: p, q => mergeWithAux lt comb x p (mergeWith p) q

/-- `mergeWith` preserves any sum semantics that is additive in the combined values. -/
theorem sum_map_mergeWith {A : Type*} [AddCommMonoid A] (ev : K × V → A)
    (hev : ∀ k x y, ev (k, comb x y) = ev (k, x) + ev (k, y)) :
    ∀ p q : List (K × V),
      ((mergeWith lt comb p q).map ev).sum = (p.map ev).sum + (q.map ev).sum := by
  intro p
  induction p with
  | nil => intro q; simp [mergeWith]
  | cons x p ih =>
    intro q
    induction q with
    | nil => simp [mergeWith, mergeWithAux]
    | cons y q ihq =>
      simp only [mergeWith] at ihq ⊢
      unfold mergeWithAux
      split_ifs with h1 h2
      · have hx : x = (x.1, x.2) := rfl
        have hy : y = (x.1, y.2) := by rw [h1]
        simp only [List.map_cons, List.sum_cons, ih, hev]
        conv_rhs => rw [hx, hy]
        abel
      · simp only [List.map_cons, List.sum_cons, ih]
        abel
      · simp only [List.map_cons, List.sum_cons] at ihq ⊢
        rw [ihq]
        abel

/-- The merge of two term lists sorted by `lt`, adding the coefficients of equal keys. -/
def mergeAdd : List (K × ℤ) → List (K × ℤ) → List (K × ℤ) := mergeWith lt (· + ·)

theorem levalBy_mergeAdd [CommRing R] (m : K → R) (p q : List (K × ℤ)) :
    levalBy m (mergeAdd lt p q) = levalBy m p + levalBy m q :=
  sum_map_mergeWith lt (· + ·) (fun e : K × ℤ => (e.2 : R) * m e.1)
    (fun k x y => by push_cast; ring) p q

end merge

section ops
variable [CommRing R] (m : K → R)

/-- Multiply every coefficient by `c`. -/
def scaleTerms (c : ℤ) (p : List (K × ℤ)) : List (K × ℤ) := p.map fun e => (e.1, c * e.2)

theorem levalBy_scaleTerms (c : ℤ) (p : List (K × ℤ)) :
    levalBy m (scaleTerms c p) = c * levalBy m p := by
  induction p with
  | nil => simp [scaleTerms]
  | cons e p ih =>
    simp only [scaleTerms, List.map_cons, levalBy_cons, Int.cast_mul] at ih ⊢
    rw [ih]
    ring

/-- Drop the terms with coefficient zero. -/
def dropZeros (p : List (K × ℤ)) : List (K × ℤ) := p.filter fun e => e.2 != 0

theorem levalBy_dropZeros (p : List (K × ℤ)) : levalBy m (dropZeros p) = levalBy m p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    by_cases h : e.2 = 0
    · simp [dropZeros, h] at ih ⊢
      exact ih
    · simp [dropZeros, h] at ih ⊢
      exact ih

end ops

/-- List equality as a `Bool` whose recursive call sits behind `&&`, so that the kernel checks
long lists without nesting one frame per element (the `DecidableEq` instance of `List` nests). -/
def listBEq {α : Type*} [DecidableEq α] : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && listBEq xs ys
  | _, _ => false

theorem eq_of_listBEq {α : Type*} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, listBEq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [listBEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, eq_of_listBEq h.2]
  | [], _ :: _, h => by simp [listBEq] at h
  | _ :: _, [], h => by simp [listBEq] at h

end KAM.EffectiveStability.Tube

end
