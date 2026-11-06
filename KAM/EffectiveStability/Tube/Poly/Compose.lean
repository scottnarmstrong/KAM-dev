/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.Sparse
public import Mathlib.Data.Fin.VecNotation

/-!
# Composition of bihomogeneous polynomials with a linear substitution (T2-CONF, N5a)

Monomials in three variables are exponent triples `Mon = ℕ × ℕ × ℕ`, `mon b w = w₀^b₀ w₁^b₁ w₂^b₂`.
A polynomial in `(z, z̄)` is a term list with keys `(a, a') : Mon × Mon`, denoting
`Σ c · z^a · z̄^{a'}` (`bevalAt`; the two arguments are independent variables).

* `symPow M a`: the symmetric power row `S[a, ·]`, built by peeling one linear factor
  `z_j = Σ_k M_jk w_k` at a time; `peval_symPow : Σ_b S[a, b] w^b = Π_j (Σ_k M_jk w_k)^{a_j}`.
* `composeLin M C`: the composition `Σ_{a, a'} c_{a a'} (M w)^a (M v)^{a'}` expanded in `(w, v)`,
  i.e. in each degree the coefficient matrix `S_dᵀ C_d S_d`, computed as
  `Σ_a S[a] ⊗ (Σ_{a'} c_{a a'} S[a'])` over the rows of `C` grouped by `a`.
  `bevalAt_composeLin : bevalAt (composeLin M C) w v = bevalAt C (M w) (M v)`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

/-- Exponent triples. -/
abbrev Mon := ℕ × ℕ × ℕ

/-- The monomial `w₀^b₀ w₁^b₁ w₂^b₂`. -/
def mon {R : Type*} [CommRing R] (b : Mon) (w : Fin 3 → R) : R :=
  w 0 ^ b.1 * w 1 ^ b.2.1 * w 2 ^ b.2.2

/-- The total degree `|b|` of an exponent triple. -/
def Mon.deg (b : Mon) : ℕ := b.1 + b.2.1 + b.2.2

/-- The lexicographic order of exponent triples. -/
def monLt (a b : Mon) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- The lexicographic order of pairs of exponent triples. -/
def biLt (a b : Mon × Mon) : Bool :=
  monLt a.1 b.1 || (a.1 == b.1 && monLt a.2 b.2)

/-- An integer 3×3 matrix as three rows. -/
abbrev Mat3 := (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)

/-- Row `j` of `M`. -/
def Mat3.row (M : Mat3) : Fin 3 → ℤ × ℤ × ℤ := ![M.1, M.2.1, M.2.2]

/-- The entry `M_jk`. -/
def Mat3.entry (M : Mat3) (j k : Fin 3) : ℤ := ![(M.row j).1, (M.row j).2.1, (M.row j).2.2] k

/-- The linear form `l₀ w₀ + l₁ w₁ + l₂ w₂`. -/
def linForm {R : Type*} [CommRing R] (l : ℤ × ℤ × ℤ) (w : Fin 3 → R) : R :=
  (l.1 : R) * w 0 + (l.2.1 : R) * w 1 + (l.2.2 : R) * w 2

/-- `(M w)_j = Σ_k M_jk w_k`. -/
def Mat3.apply {R : Type*} [CommRing R] (M : Mat3) (w : Fin 3 → R) : Fin 3 → R :=
  fun j => linForm (M.row j) w

/-- Polynomials in one set of three variables. -/
def pevalAt {R : Type*} [CommRing R] (p : List (Mon × ℤ)) (w : Fin 3 → R) : R :=
  levalBy (fun b => mon b w) p

/-- Polynomials in `(w, v)`. -/
def bevalAt {R : Type*} [CommRing R] (p : List ((Mon × Mon) × ℤ)) (w v : Fin 3 → R) : R :=
  levalBy (fun b => mon b.1 w * mon b.2 v) p

/-- Multiply by `c · w₀`, `c · w₁`, `c · w₂`. -/
def shift0 (c : ℤ) (p : List (Mon × ℤ)) : List (Mon × ℤ) :=
  p.map fun e => ((e.1.1 + 1, e.1.2.1, e.1.2.2), c * e.2)

def shift1 (c : ℤ) (p : List (Mon × ℤ)) : List (Mon × ℤ) :=
  p.map fun e => ((e.1.1, e.1.2.1 + 1, e.1.2.2), c * e.2)

def shift2 (c : ℤ) (p : List (Mon × ℤ)) : List (Mon × ℤ) :=
  p.map fun e => ((e.1.1, e.1.2.1, e.1.2.2 + 1), c * e.2)

/-- Multiply by the linear form `l`. -/
def mulLin (l : ℤ × ℤ × ℤ) (p : List (Mon × ℤ)) : List (Mon × ℤ) :=
  mergeAdd monLt (shift0 l.1 p) (mergeAdd monLt (shift1 l.2.1 p) (shift2 l.2.2 p))

/-- Multiply `n` times by the linear form `l`. -/
def mulLinPow (l : ℤ × ℤ × ℤ) : ℕ → List (Mon × ℤ) → List (Mon × ℤ)
  | 0, p => p
  | n + 1, p => mulLin l (mulLinPow l n p)

/-- The symmetric-power row `S[a, ·]`: `Π_j (Σ_k M_jk w_k)^{a_j}` expanded in `w`. -/
def symPow (M : Mat3) (a : Mon) : List (Mon × ℤ) :=
  mulLinPow M.2.2 a.2.2 (mulLinPow M.2.1 a.2.1 (mulLinPow M.1 a.1 [((0, 0, 0), 1)]))

/-- The outer product `p(w) q(v)`. -/
def outerTerms (p q : List (Mon × ℤ)) : List ((Mon × Mon) × ℤ) :=
  p.flatMap fun e => q.map fun f => ((e.1, f.1), e.2 * f.2)

/-- Insert the term `(a', c)` into the row of `a` of a grouped polynomial. -/
def groupInsert (a a' : Mon) (c : ℤ) : List (Mon × List (Mon × ℤ)) → List (Mon × List (Mon × ℤ))
  | [] => [(a, [(a', c)])]
  | g :: G =>
    if g.1 = a then (a, mergeAdd monLt [(a', c)] g.2) :: G
    else if monLt a g.1 then (a, [(a', c)]) :: g :: G else g :: groupInsert a a' c G

/-- Group the terms of a polynomial in `(z, z̄)` by the `z`-exponent. -/
def groupTerms (C : List ((Mon × Mon) × ℤ)) : List (Mon × List (Mon × ℤ)) :=
  C.foldr (fun e G => groupInsert e.1.1 e.1.2 e.2 G) []

/-- Group a polynomial given in chunks: each chunk is grouped separately (the kernel nests one frame
per term of a chunk) and the groupings are merged. -/
def groupChunks (Cs : List (List ((Mon × Mon) × ℤ))) : List (Mon × List (Mon × ℤ)) :=
  Cs.foldr (fun C G => mergeWith monLt (mergeAdd monLt) (groupTerms C) G) []

/-- `Σ_{a'} c_{a a'} S[a', ·]` for one row of `C`. -/
def rowComb (M : Mat3) (row : List (Mon × ℤ)) : List (Mon × ℤ) :=
  row.foldr (fun e acc => mergeAdd monLt (scaleTerms e.2 (symPow M e.1)) acc) []

/-- **The composition with `z = M w`, `z̄ = M v`**: `Σ_a S[a] ⊗ (Σ_{a'} c_{a a'} S[a'])`. -/
def composeLin (M : Mat3) (Cs : List (List ((Mon × Mon) × ℤ))) : List ((Mon × Mon) × ℤ) :=
  dropZeros ((groupChunks Cs).foldr
    (fun g acc => mergeAdd biLt (outerTerms (symPow M g.1) (rowComb M g.2)) acc) [])

/-! ### Semantics -/

section semantics
variable {R : Type*} [CommRing R]

@[simp] theorem pevalAt_nil (w : Fin 3 → R) : pevalAt ([] : List (Mon × ℤ)) w = 0 := rfl

@[simp] theorem pevalAt_cons (e : Mon × ℤ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (e :: p) w = (e.2 : R) * mon e.1 w + pevalAt p w :=
  levalBy_cons _ e p

@[simp] theorem bevalAt_cons (e : (Mon × Mon) × ℤ) (p : List ((Mon × Mon) × ℤ)) (w v : Fin 3 → R) :
    bevalAt (e :: p) w v = (e.2 : R) * (mon e.1.1 w * mon e.1.2 v) + bevalAt p w v :=
  levalBy_cons _ e p

@[simp] theorem bevalAt_nil (w v : Fin 3 → R) : bevalAt ([] : List ((Mon × Mon) × ℤ)) w v = 0 :=
  rfl

theorem bevalAt_append (p q : List ((Mon × Mon) × ℤ)) (w v : Fin 3 → R) :
    bevalAt (p ++ q) w v = bevalAt p w v + bevalAt q w v :=
  levalBy_append _ p q

theorem pevalAt_mergeAdd (p q : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (mergeAdd monLt p q) w = pevalAt p w + pevalAt q w :=
  levalBy_mergeAdd monLt _ p q

theorem bevalAt_mergeAdd (p q : List ((Mon × Mon) × ℤ)) (w v : Fin 3 → R) :
    bevalAt (mergeAdd biLt p q) w v = bevalAt p w v + bevalAt q w v :=
  levalBy_mergeAdd biLt _ p q

theorem pevalAt_scaleTerms (c : ℤ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (scaleTerms c p) w = c * pevalAt p w :=
  levalBy_scaleTerms _ c p

theorem pevalAt_shift0 (c : ℤ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (shift0 c p) w = c * w 0 * pevalAt p w := by
  induction p with
  | nil => simp [shift0]
  | cons e p ih =>
    simp only [shift0, List.map_cons, pevalAt_cons, Int.cast_mul] at ih ⊢
    rw [ih]
    simp only [mon]
    ring

theorem pevalAt_shift1 (c : ℤ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (shift1 c p) w = c * w 1 * pevalAt p w := by
  induction p with
  | nil => simp [shift1]
  | cons e p ih =>
    simp only [shift1, List.map_cons, pevalAt_cons, Int.cast_mul] at ih ⊢
    rw [ih]
    simp only [mon]
    ring

theorem pevalAt_shift2 (c : ℤ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (shift2 c p) w = c * w 2 * pevalAt p w := by
  induction p with
  | nil => simp [shift2]
  | cons e p ih =>
    simp only [shift2, List.map_cons, pevalAt_cons, Int.cast_mul] at ih ⊢
    rw [ih]
    simp only [mon]
    ring

theorem pevalAt_mulLin (l : ℤ × ℤ × ℤ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (mulLin l p) w = linForm l w * pevalAt p w := by
  simp only [mulLin, pevalAt_mergeAdd, pevalAt_shift0, pevalAt_shift1, pevalAt_shift2, linForm]
  ring

theorem pevalAt_mulLinPow (l : ℤ × ℤ × ℤ) (n : ℕ) (p : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (mulLinPow l n p) w = linForm l w ^ n * pevalAt p w := by
  induction n with
  | zero => simp [mulLinPow]
  | succ n ih => rw [mulLinPow, pevalAt_mulLin, ih]; ring

/-- **Symmetric powers**: `Σ_b S[a, b] w^b = Π_j (Σ_k M_jk w_k)^{a_j}`. -/
theorem pevalAt_symPow (M : Mat3) (a : Mon) (w : Fin 3 → R) :
    pevalAt (symPow M a) w = mon a (M.apply w) := by
  simp only [symPow, pevalAt_mulLinPow, pevalAt_cons, pevalAt_nil, mon, Mat3.apply, Mat3.row]
  simp
  ring

theorem bevalAt_outerTerms (p q : List (Mon × ℤ)) (w v : Fin 3 → R) :
    bevalAt (outerTerms p q) w v = pevalAt p w * pevalAt q v := by
  induction p with
  | nil => simp [outerTerms]
  | cons e p ih =>
    simp only [outerTerms, List.flatMap_cons, bevalAt_append] at ih ⊢
    rw [ih]
    have : ∀ q : List (Mon × ℤ), bevalAt (q.map fun f => ((e.1, f.1), e.2 * f.2)) w v =
        e.2 * mon e.1 w * pevalAt q v := by
      intro q
      induction q with
      | nil => simp
      | cons f q ihq =>
        simp only [List.map_cons, bevalAt_cons, pevalAt_cons, Int.cast_mul] at ihq ⊢
        rw [ihq]
        ring
    rw [this, pevalAt_cons]
    ring

/-- The value of a grouped polynomial `Σ_{(a, row)} w^a · row(v)`. -/
def gevalAt (G : List (Mon × List (Mon × ℤ))) (w v : Fin 3 → R) : R :=
  (G.map fun g => mon g.1 w * pevalAt g.2 v).sum

theorem gevalAt_groupInsert (a a' : Mon) (c : ℤ) (G : List (Mon × List (Mon × ℤ)))
    (w v : Fin 3 → R) :
    gevalAt (groupInsert a a' c G) w v = c * (mon a w * mon a' v) + gevalAt G w v := by
  induction G with
  | nil => simp [groupInsert, gevalAt]; ring
  | cons g G ih =>
    unfold groupInsert
    split_ifs with h1 h2
    · simp only [gevalAt, List.map_cons, List.sum_cons, pevalAt_mergeAdd, pevalAt_cons,
        pevalAt_nil, h1]
      ring
    · simp only [gevalAt, List.map_cons, List.sum_cons, pevalAt_cons, pevalAt_nil]
      ring
    · simp only [gevalAt, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem gevalAt_groupTerms (C : List ((Mon × Mon) × ℤ)) (w v : Fin 3 → R) :
    gevalAt (groupTerms C) w v = bevalAt C w v := by
  induction C with
  | nil => rfl
  | cons e C ih =>
    simp only [groupTerms, List.foldr_cons] at ih ⊢
    rw [gevalAt_groupInsert, ih, bevalAt_cons]

theorem gevalAt_mergeWith (G H : List (Mon × List (Mon × ℤ))) (w v : Fin 3 → R) :
    gevalAt (mergeWith monLt (mergeAdd monLt) G H) w v = gevalAt G w v + gevalAt H w v :=
  sum_map_mergeWith monLt (mergeAdd monLt) (fun g => mon g.1 w * pevalAt g.2 v)
    (fun k x y => by simp only [pevalAt_mergeAdd]; ring) G H

theorem gevalAt_groupChunks (Cs : List (List ((Mon × Mon) × ℤ))) (w v : Fin 3 → R) :
    gevalAt (groupChunks Cs) w v = bevalAt Cs.flatten w v := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
    simp only [groupChunks, List.foldr_cons, List.flatten_cons] at ih ⊢
    rw [gevalAt_mergeWith, ih, gevalAt_groupTerms, bevalAt_append]

theorem pevalAt_rowComb (M : Mat3) (row : List (Mon × ℤ)) (w : Fin 3 → R) :
    pevalAt (rowComb M row) w = pevalAt row (M.apply w) := by
  induction row with
  | nil => rfl
  | cons e row ih =>
    simp only [rowComb, List.foldr_cons] at ih ⊢
    rw [pevalAt_mergeAdd, ih, pevalAt_scaleTerms, pevalAt_symPow, pevalAt_cons]

/-- **The composition theorem**: `composeLin M Cs` is the polynomial `C(M w, M v)` in `(w, v)`,
where `C` is the concatenation of the chunks `Cs`. In degree `d` its coefficient matrix is
`S_dᵀ C_d S_d`. -/
theorem bevalAt_composeLin (M : Mat3) (Cs : List (List ((Mon × Mon) × ℤ))) (w v : Fin 3 → R) :
    bevalAt (composeLin M Cs) w v = bevalAt Cs.flatten (M.apply w) (M.apply v) := by
  have key : ∀ G : List (Mon × List (Mon × ℤ)),
      bevalAt (G.foldr (fun g acc => mergeAdd biLt (outerTerms (symPow M g.1) (rowComb M g.2)) acc)
        []) w v = gevalAt G (M.apply w) (M.apply v) := by
    intro G
    induction G with
    | nil => rfl
    | cons g G ih =>
      rw [List.foldr_cons, bevalAt_mergeAdd, ih, bevalAt_outerTerms, pevalAt_symPow,
        pevalAt_rowComb]
      simp [gevalAt]
  rw [composeLin, bevalAt, levalBy_dropZeros, ← bevalAt, key, gevalAt_groupChunks]

theorem Mat3.apply_eq (M : Mat3) (w : Fin 3 → R) (j : Fin 3) :
    M.apply w j = (M.entry j 0 : R) * w 0 + (M.entry j 1 : R) * w 1 + (M.entry j 2 : R) * w 2 := by
  rfl

end semantics

end KAM.EffectiveStability.Tube

end
