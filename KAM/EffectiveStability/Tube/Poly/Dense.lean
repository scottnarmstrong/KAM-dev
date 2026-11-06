/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.Compose
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Dense coefficient matrices and the composition `Sᵀ C S` in small steps (T2-CONF, N5a)

In a fixed degree the monomials form a list `A` (no duplicates), and a homogeneous polynomial is a
dense row `r : List ℤ` aligned with `A` (`rowEval A r w = Σ_k r_k w^{A_k}`). The composition
`H = Sᵀ C S` of a polynomial `C(z, z̄)` with `z = M w` is verified in steps that each touch one row:
* `S_i = symPow M (A i)` (the symmetric-power rows; `rowEval A S_i w = (M w)^{A i}`);
* `T_i = Σ_j C(A i, A j) S_j` (`linComb`), with `C(a, b) = rowSum L a b` read off the term list `L`;
* `H_k = Σ_i S_i[k] T_i`.
`bevalAt_eq_dense`: then `C(M w, M v) = Σ_k w^{A_k} (Σ_l H_k[l] v^{A_l})`. No step merges long
lists, so every kernel check stays small.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset

/-- `Σ_k r_k w^{A_k}` (the two lists are zipped). -/
def rowEval {R : Type*} [CommRing R] (A : List Mon) (r : List ℤ) (w : Fin 3 → R) : R :=
  pevalAt (A.zip r) w

/-- Entrywise sum of rows. -/
def vecAdd (x y : List ℤ) : List ℤ := List.zipWith (· + ·) x y

/-- A multiple of a row. -/
def vecScale (c : ℤ) (x : List ℤ) : List ℤ := x.map (c * ·)

/-- `Σ_j c_j r_j` over the zipped lists, starting from the zero row of length `n`. -/
def linComb (n : ℕ) : List ℤ → List (List ℤ) → List ℤ
  | c :: cs, r :: rs => vecAdd (vecScale c r) (linComb n cs rs)
  | _, _ => List.replicate n 0

/-- The coefficient of `z^a z̄^b` in a term list. -/
def rowSum (L : List ((Mon × Mon) × ℤ)) (a b : Mon) : ℤ :=
  ((L.filter fun e => decide (e.1 = (a, b))).map (·.2)).sum

/-- Row `a` of the coefficient matrix of `L` along the monomial list `A`. -/
def cRowOf (A : List Mon) (L : List ((Mon × Mon) × ℤ)) (a : Mon) : List ℤ :=
  let La := L.filter fun e => decide (e.1.1 = a)
  A.map fun b => rowSum La a b

section semantics
variable {R : Type*} [CommRing R]

theorem rowEval_vecAdd : ∀ (A : List Mon) (x y : List ℤ), x.length = A.length →
    y.length = A.length → ∀ w : Fin 3 → R,
      rowEval A (vecAdd x y) w = rowEval A x w + rowEval A y w
  | [], _, _, _, _, w => by simp [rowEval, pevalAt, levalBy]
  | a :: A, x :: xs, y :: ys, hx, hy, w => by
    simp only [List.length_cons, add_left_inj] at hx hy
    have ih := rowEval_vecAdd A xs ys hx hy w
    simp only [rowEval, vecAdd, List.zipWith_cons_cons, List.zip_cons_cons, pevalAt_cons,
      Int.cast_add] at ih ⊢
    rw [ih]; ring
  | _ :: _, [], _, hx, _, _ => by simp at hx
  | _ :: _, _ :: _, [], _, hy, _ => by simp at hy

theorem rowEval_vecScale (c : ℤ) : ∀ (A : List Mon) (x : List ℤ) (w : Fin 3 → R),
    rowEval A (vecScale c x) w = c * rowEval A x w
  | [], _, w => by simp [rowEval, pevalAt, levalBy]
  | _ :: _, [], w => by simp [rowEval, vecScale, pevalAt, levalBy]
  | a :: A, x :: xs, w => by
    have ih := rowEval_vecScale c A xs w
    simp only [rowEval, vecScale, List.map_cons, List.zip_cons_cons, pevalAt_cons,
      Int.cast_mul] at ih ⊢
    rw [ih]; ring

theorem rowEval_replicate_zero : ∀ (A : List Mon) (n : ℕ) (w : Fin 3 → R),
    rowEval A (List.replicate n 0) w = 0
  | [], _, w => by simp [rowEval, pevalAt, levalBy]
  | _ :: _, 0, w => by simp [rowEval, pevalAt, levalBy]
  | a :: A, n + 1, w => by
    have ih := rowEval_replicate_zero A n w
    simp only [rowEval, List.replicate_succ, List.zip_cons_cons, pevalAt_cons] at ih ⊢
    rw [ih]; simp

theorem length_vecAdd (x y : List ℤ) : (vecAdd x y).length = min x.length y.length := by
  simp [vecAdd]

theorem length_linComb (n : ℕ) : ∀ (cs : List ℤ) (rs : List (List ℤ)),
    (∀ r ∈ rs, r.length = n) → (linComb n cs rs).length = n
  | c :: cs, r :: rs, h => by
    simp only [linComb, length_vecAdd, vecScale, List.length_map]
    rw [h r List.mem_cons_self,
      length_linComb n cs rs fun r' hr' => h r' (List.mem_cons_of_mem r hr'),
      min_self]
  | [], _, _ => by simp [linComb]
  | _ :: _, [], _ => by simp [linComb]

/-- `rowEval A (Σ_j c_j r_j) = Σ_j c_j rowEval A r_j` for rows of length `|A|`. -/
theorem rowEval_linComb (A : List Mon) (w : Fin 3 → R) : ∀ (cs : List ℤ) (rs : List (List ℤ)),
    (∀ r ∈ rs, r.length = A.length) →
      rowEval A (linComb A.length cs rs) w =
        ((cs.zip rs).map fun p => (p.1 : R) * rowEval A p.2 w).sum
  | c :: cs, r :: rs, h => by
    have hr := h r List.mem_cons_self
    have hrs : ∀ r' ∈ rs, r'.length = A.length := fun r' hr' => h r' (List.mem_cons_of_mem r hr')
    rw [linComb, rowEval_vecAdd A _ _ (by simp [vecScale, hr]) (length_linComb _ cs rs hrs),
      rowEval_vecScale, rowEval_linComb A w cs rs hrs]
    simp
  | [], _, _ => by simp [linComb, rowEval_replicate_zero]
  | _ :: _, [], _ => by simp [linComb, rowEval_replicate_zero]

/-- Regrouping a list sum by a key whose values lie in a finset. -/
theorem list_sum_eq_sum_filter {α κ : Type*} [DecidableEq κ] (key : α → κ) (f : α → R)
    (S : Finset κ) : ∀ l : List α, (∀ a ∈ l, key a ∈ S) →
      (l.map f).sum = ∑ n ∈ S, ((l.filter fun a => decide (key a = n)).map f).sum
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons,
      list_sum_eq_sum_filter key f S l (fun b hb => h b (List.mem_cons_of_mem a hb))]
    have ha : key a ∈ S := h a List.mem_cons_self
    rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ ha, ← add_assoc]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun n hn => ?_
      have : key a ≠ n := fun h' => (Finset.ne_of_mem_erase hn) h'.symm
      simp [this]

theorem getD_map_of_lt {α β : Type*} (f : α → β) {l : List α} {j : ℕ} (hj : j < l.length)
    (d : α) (d' : β) : (l.map f).getD j d' = f (l.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem getD_mem {α : Type*} {l : List α} {j : ℕ} (hj : j < l.length) (d : α) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _

/-- A zipped list sum as an index sum. -/
theorem sum_zip_eq_sum_range {α β : Type*} [Inhabited α] [Inhabited β] (g : α → β → R) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      ((l₁.zip l₂).map fun p => g p.1 p.2).sum =
        ∑ i ∈ range l₁.length, g (l₁.getD i default) (l₂.getD i default)
  | [], [], _ => by simp
  | x :: l₁, y :: l₂, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, sum_zip_eq_sum_range g l₁ l₂ h,
      List.length_cons, Finset.sum_range_succ']
    simp [add_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem rowEval_eq_sum (A : List Mon) (r : List ℤ) (hr : r.length = A.length) (w : Fin 3 → R) :
    rowEval A r w = ∑ k ∈ range A.length, (r.getD k 0 : R) * mon (A.getD k default) w := by
  have := sum_zip_eq_sum_range (fun (b : Mon) (c : ℤ) => (c : R) * mon b w) A r hr.symm
  simpa [rowEval, pevalAt, levalBy] using this

/-- A sum over a duplicate-free list as an index sum. -/
theorem sum_toFinset_eq_sum_range {α : Type*} [Inhabited α] [DecidableEq α] (A : List α)
    (hA : A.Nodup) (f : α → R) :
    ∑ a ∈ A.toFinset, f a = ∑ i ∈ range A.length, f (A.getD i default) := by
  rw [List.sum_toFinset _ hA]
  have := sum_zip_eq_sum_range (fun (a : α) (_ : α) => f a) A A rfl
  rw [← this]
  congr 1
  rw [show (fun p : α × α => f p.1) = f ∘ Prod.fst from rfl, ← List.map_map,
    List.map_fst_zip (by simp)]

theorem rowSum_filter_fst (L : List ((Mon × Mon) × ℤ)) (a b : Mon) :
    rowSum (L.filter fun e => decide (e.1.1 = a)) a b = rowSum L a b := by
  simp only [rowSum, List.filter_filter]
  congr 2
  refine List.filter_congr fun e _ => ?_
  by_cases h : e.1 = (a, b)
  · simp [h]
  · simp [h]

/-- **The dense composition.** Let `A` be a duplicate-free list of monomials of length `n`, `L` a
term list with all keys in `A × A`, and `S`, `T`, `H` lists of `n` rows of length `n` with
`symPow M (A i) = A.zip S_i`, `T_i = Σ_j C(A i, A j) S_j` and `H_k = Σ_i S_i[k] T_i` (`k < n`). Then
`C(M w, M v) = Σ_k w^{A_k} rowEval A H_k v`. -/
theorem bevalAt_eq_dense (M : Mat3) (A : List Mon) (hA : A.Nodup) (L : List ((Mon × Mon) × ℤ))
    (hL : ∀ e ∈ L, e.1.1 ∈ A ∧ e.1.2 ∈ A) (S T H : List (List ℤ))
    (hSl : S.length = A.length) (hTl : T.length = A.length)
    (hSr : ∀ r ∈ S, r.length = A.length) (hTr : ∀ r ∈ T, r.length = A.length)
    (hS : ∀ i < A.length, symPow M (A.getD i default) = A.zip (S.getD i []))
    (hT : ∀ i < A.length, T.getD i [] = linComb A.length (cRowOf A L (A.getD i default)) S)
    (hH : ∀ k < A.length, H.getD k [] = linComb A.length (S.map fun r => r.getD k 0) T)
    (w v : Fin 3 → R) :
    bevalAt L (M.apply w) (M.apply v) =
      ∑ k ∈ range A.length, mon (A.getD k default) w * rowEval A (H.getD k []) v := by
  set n := A.length with hn
  -- (1) the rows of `S`
  have h1 : ∀ i < n, ∀ x : Fin 3 → R,
      rowEval A (S.getD i []) x = mon (A.getD i default) (M.apply x) := by
    intro i hi x
    rw [← pevalAt_symPow, hS i hi, rowEval]
  -- (2) the rows of `T`
  have h2 : ∀ i < n, rowEval A (T.getD i []) v =
      ∑ j ∈ range n, (rowSum L (A.getD i default) (A.getD j default) : R) *
        mon (A.getD j default) (M.apply v) := by
    intro i hi
    have hz := sum_zip_eq_sum_range (fun (c : ℤ) (r : List ℤ) => (c : R) * rowEval A r v)
      (cRowOf A L (A.getD i default)) S (by simp [cRowOf, hSl, hn])
    rw [hT i hi, rowEval_linComb A v _ _ hSr, hz]
    simp only [cRowOf, List.length_map]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n := Finset.mem_range.1 hj
    rw [show S.getD j default = S.getD j [] from rfl, h1 j hj' v, getD_map_of_lt _ hj' default,
      rowSum_filter_fst]
  -- (3) the rows of `H`
  have h3 : ∀ k < n, rowEval A (H.getD k []) v =
      ∑ i ∈ range n, ((S.getD i []).getD k 0 : R) * rowEval A (T.getD i []) v := by
    intro k hk
    have hz := sum_zip_eq_sum_range (fun (c : ℤ) (r : List ℤ) => (c : R) * rowEval A r v)
      (S.map fun r => r.getD k 0) T (by simp [hSl, hTl])
    rw [hH k hk, rowEval_linComb A v _ _ hTr, hz]
    simp only [List.length_map, hSl]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < S.length := by rw [hSl]; exact Finset.mem_range.1 hi
    rw [getD_map_of_lt _ hi' [] default]
    rfl
  -- (4) assemble
  have hrhs : ∑ k ∈ range n, mon (A.getD k default) w * rowEval A (H.getD k []) v =
      ∑ i ∈ range n, mon (A.getD i default) (M.apply w) * rowEval A (T.getD i []) v := by
    rw [Finset.sum_congr rfl fun k hk => by rw [h3 k (Finset.mem_range.1 hk)]]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.1 hi
    have hSi : (S.getD i []).length = n := hSr _ (getD_mem (by rw [hSl]; exact hi') [])
    rw [← h1 i hi' w, rowEval_eq_sum A _ hSi, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hrhs]
  -- (5) regroup `L` by its keys
  have hreg : bevalAt L (M.apply w) (M.apply v) =
      ∑ p ∈ A.toFinset ×ˢ A.toFinset,
        (rowSum L p.1 p.2 : R) * (mon p.1 (M.apply w) * mon p.2 (M.apply v)) := by
    rw [bevalAt, levalBy, list_sum_eq_sum_filter (fun e : (Mon × Mon) × ℤ => e.1) _
      (A.toFinset ×ˢ A.toFinset) L
      (fun e he => Finset.mem_product.2 ⟨List.mem_toFinset.2 (hL e he).1,
        List.mem_toFinset.2 (hL e he).2⟩)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [rowSum, Prod.mk.eta]
    rw [Int.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun e he => ?_
    have := (List.mem_filter.1 he).2
    simp only [decide_eq_true_eq] at this
    simp [this]
  rw [hreg, Finset.sum_product, sum_toFinset_eq_sum_range A hA]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h2 i (Finset.mem_range.1 hi), sum_toFinset_eq_sum_range A hA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The term list of a dense matrix `H` along `A`: the entry `H_k[l]` at the key `(A k, A l)`. -/
def denseRows (A : List Mon) (H : List (List ℤ)) : List ((Mon × Mon) × ℤ) :=
  (A.zip H).flatMap fun p => (A.zip p.2).map fun q => ((p.1, q.1), q.2)

theorem bevalAt_denseRows (A : List Mon) (H : List (List ℤ)) (hHl : H.length = A.length)
    (w v : Fin 3 → R) :
    bevalAt (denseRows A H) w v =
      ∑ k ∈ range A.length, mon (A.getD k default) w * rowEval A (H.getD k []) v := by
  have hrow : ∀ (a : Mon) (r : List ℤ), bevalAt ((A.zip r).map fun q => ((a, q.1), q.2)) w v =
      mon a w * rowEval A r v := by
    intro a r
    simp only [bevalAt, levalBy, rowEval, pevalAt, List.map_map]
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp]
    ring
  have hz := sum_zip_eq_sum_range (fun (a : Mon) (r : List ℤ) => mon a w * rowEval A r v) A H
    hHl.symm
  rw [show (∑ k ∈ range A.length, mon (A.getD k default) w * rowEval A (H.getD k []) v) =
      ∑ i ∈ range A.length, mon (A.getD i default) w * rowEval A (H.getD i default) v from rfl,
    ← hz, denseRows]
  induction A.zip H with
  | nil => rfl
  | cons p l ih =>
    rw [List.flatMap_cons, bevalAt_append, ih, hrow, List.map_cons, List.sum_cons]

theorem mem_denseRows {A : List Mon} {H : List (List ℤ)} {e : (Mon × Mon) × ℤ}
    (he : e ∈ denseRows A H) : e.1.1 ∈ A ∧ e.1.2 ∈ A := by
  simp only [denseRows, List.mem_flatMap, List.mem_map] at he
  obtain ⟨p, hp, q, hq, rfl⟩ := he
  exact ⟨(List.of_mem_zip hp).1, (List.of_mem_zip hq).1⟩

end semantics

end KAM.EffectiveStability.Tube

end
