/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Powers
public import KAM.EffectiveStability.Tube.Poly.HtDense
public import KAM.EffectiveStability.Tube.Poly.HTilde
public import KAM.EffectiveStability.Tube.Poly.Center
public import KAM.EffectiveStability.Tube.Witness.HalfPow

/-!
# The nested Horner sums are the Taylor coefficients (T2-CONF, N5a-2)

N7's Horner stage evaluates `h_m` by three nested sums over the exponent groups `n ∈ D.ns`
(`HData.Ut`, `Vt`, `Ht`, `Tube/Engine/Horner.lean`), with filters that drop only terms with a zero
binomial factor or an empty sub-sum. `HData.Ht_eq_sum` flattens them:
`Ht m φ = Σ_{n ∈ ns} gb(n₁, m₁) gb(n₂, m₂) gb(n₃, m₃) T_n(φ) P₀(n₁ - 2m₁) P₁(n₂ - 2m₂)
P₂(n₃ - 2m₃)`.
This is pure list regrouping; no data is involved.

The bridge to N5a's real functions (`HData.Ht_eq_hCoef`): with `Tt = D.Tt` (`denseCos CT (Tdat n)`)
and `Pt = D.Pt` (`√B_j^k`, `B_j = denseCos CP (Bdat j)`), `Ht` is N5a's Taylor coefficient
`hCoef E N rows B m = Σ_n T_n Π_j binom(n_j/2, m_j) B_j^{n_j/2 - m_j}`, given the data equalities
`D.Tt n = Tn E N rows n`, `D.Bt j = B_j`, `B > 0` and that every row exponent is a group of `D.ns`.
The data equalities reduce to kernel checks of dense lists:
* `Tn_eq_denseCos`: `T_n = denseCos C (pDense C (tTerms E N rows n))` (modes in the box);
* `tubeCenter_eq_denseCos`: N6's tube centre is `denseCos C (scatter … (bPairs C modes Ibar j))`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

/-- A filter that drops only zero terms does not change a list sum. -/
theorem sum_filter_of_zero {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ)
    (h : ∀ x ∈ l, p x = false → f x = 0) : ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · simp [hp, ih']
    · simp [hp, ih', h x List.mem_cons_self (by simpa using hp)]

/-- Regrouping a list sum by a natural key bounded by `N`. -/
theorem sum_regroup_range {α : Type*} (l : List α) (key : α → ℕ) (N : ℕ)
    (hk : ∀ x ∈ l, key x ≤ N) (f : α → ℝ) :
    (l.map f).sum =
      ((List.range (N + 1)).map fun k => ((l.filter fun x => key x == k).map f).sum).sum := by
  rw [list_sum_eq_sum_filter key f (Finset.range (N + 1)) l
      (fun x hx => Finset.mem_range.2 (Nat.lt_succ_of_le (hk x hx))),
    sum_map_range_g]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2

theorem mul_list_sum {α : Type*} (a : ℝ) (l : List α) (f : α → ℝ) :
    a * (l.map f).sum = (l.map fun x => a * f x).sum := (List.sum_map_mul_left ..).symm

theorem list_sum_mul {α : Type*} (a : ℝ) (l : List α) (f : α → ℝ) :
    (l.map f).sum * a = (l.map fun x => f x * a).sum := (List.sum_map_mul_right ..).symm

namespace HData

variable (D : HData) (Tt : ℕ × ℕ × ℕ → (Fin 2 → ℝ) → ℝ) (Pt : ℕ → ℤ → (Fin 2 → ℝ) → ℝ)

theorem Ut_eq (hb : ∀ n ∈ D.ns, n.1 ≤ D.Nmax ∧ n.2.1 ≤ D.Nmax ∧ n.2.2 ≤ D.Nmax)
    (n1 n2 m3 : ℕ) (φ : Fin 2 → ℝ) :
    D.Ut Tt Pt n1 n2 m3 φ = ((D.ns.filter fun n => n.1 == n1 && n.2.1 == n2).map fun n =>
      (gbQ n.2.2 m3 : ℝ) * (Tt n φ * Pt 2 ((n.2.2 : ℤ) - 2 * m3) φ)).sum := by
  have hu : D.uIdx n1 n2 m3 = (D.ns.filter fun n => n.1 == n1 && n.2.1 == n2).filter
      fun n => gbQ n.2.2 m3 != 0 && decide (n.2.2 ≤ D.Nmax) := by
    rw [uIdx, List.filter_filter]
    refine List.filter_congr fun n _ => ?_
    cases (n.1 == n1) <;> cases (n.2.1 == n2) <;> cases (gbQ n.2.2 m3 != 0) <;>
      cases decide (n.2.2 ≤ D.Nmax) <;> rfl
  rw [Ut, hu, sum_filter_of_zero]
  intro n hn hp
  have hnN := (hb n (List.mem_filter.1 hn).1).2.2
  simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at hp
  rcases hp with hg | hg
  · rw [hg]; simp
  · exact absurd hnN hg

theorem Vt_eq (n1 m2 m3 : ℕ) (φ : Fin 2 → ℝ) :
    D.Vt Tt Pt n1 m2 m3 φ = ((List.range (D.Nmax + 1)).map fun n2 =>
      (gbQ n2 m2 : ℝ) * (D.Ut Tt Pt n1 n2 m3 φ * Pt 1 ((n2 : ℤ) - 2 * m2) φ)).sum := by
  have hU0 : ∀ n2, D.uIdx n1 n2 m3 = [] → D.Ut Tt Pt n1 n2 m3 φ = 0 := by
    intro n2 h; simp [Ut, h]
  rw [Vt, vIdx, n2s, sum_filter_of_zero, sum_filter_of_zero]
  · intro n2 _ hp
    rw [hU0 n2, zero_mul, mul_zero]
    simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and] at hp
    rw [uIdx, List.filter_eq_nil_iff]
    intro n hn h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact hp n hn h.1.1.1 h.1.1.2
  · intro n2 _ hp
    simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.not_eq_false',
      List.isEmpty_iff] at hp
    rcases hp with hg | hg
    · rw [hg]; simp
    · rw [hU0 n2 hg, zero_mul, mul_zero]

theorem Ht_eq_range (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    D.Ht Tt Pt m φ = ((List.range (D.Nmax + 1)).map fun n1 =>
      (gbQ n1 m.1 : ℝ) * (D.Vt Tt Pt n1 m.2.1 m.2.2 φ * Pt 0 ((n1 : ℤ) - 2 * m.1) φ)).sum := by
  have hV0 : ∀ n1, D.vIdx n1 m.2.1 m.2.2 = [] → D.Vt Tt Pt n1 m.2.1 m.2.2 φ = 0 := by
    intro n1 h; simp [Vt, h]
  rw [Ht, hIdx, n1s, sum_filter_of_zero, sum_filter_of_zero]
  · intro n1 _ hp
    simp only [List.any_eq_false, beq_iff_eq] at hp
    have hn2 : D.n2s n1 = [] := by
      rw [n2s, List.filter_eq_nil_iff]
      intro n2 _ h
      obtain ⟨n, hn, h'⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      exact hp n hn h'.1
    rw [hV0 n1 (by simp [vIdx, hn2]), zero_mul, mul_zero]
  · intro n1 _ hp
    simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.not_eq_false',
      List.isEmpty_iff] at hp
    rcases hp with hg | hg
    · rw [hg]; simp
    · rw [hV0 n1 hg, zero_mul, mul_zero]

/-- **The flattened Horner sum** (N7's target (1)). The duplicate-freeness of `ns` is not needed:
the identity is a regrouping of list sums. -/
theorem Ht_eq_sum (_hnd : D.ns.Nodup)
    (hb : ∀ n ∈ D.ns, n.1 ≤ D.Nmax ∧ n.2.1 ≤ D.Nmax ∧ n.2.2 ≤ D.Nmax)
    (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    D.Ht Tt Pt m φ =
      (D.ns.map fun n => ((gbQ n.1 m.1 * gbQ n.2.1 m.2.1 * gbQ n.2.2 m.2.2 : ℚ) : ℝ) *
      (Tt n φ * Pt 0 ((n.1 : ℤ) - 2 * m.1) φ * Pt 1 ((n.2.1 : ℤ) - 2 * m.2.1) φ *
        Pt 2 ((n.2.2 : ℤ) - 2 * m.2.2) φ)).sum := by
  set F : ℕ × ℕ × ℕ → ℝ := fun n => ((gbQ n.1 m.1 * gbQ n.2.1 m.2.1 * gbQ n.2.2 m.2.2 : ℚ) : ℝ) *
      (Tt n φ * Pt 0 ((n.1 : ℤ) - 2 * m.1) φ * Pt 1 ((n.2.1 : ℤ) - 2 * m.2.1) φ *
        Pt 2 ((n.2.2 : ℤ) - 2 * m.2.2) φ) with hF
  -- regroup the right side by `n₁`, then by `n₂`
  rw [sum_regroup_range D.ns (fun n => n.1) D.Nmax (fun n hn => (hb n hn).1) F, Ht_eq_range D Tt Pt]
  congr 1
  refine List.map_congr_left fun n1 _ => ?_
  rw [sum_regroup_range (D.ns.filter fun n => n.1 == n1) (fun n => n.2.1) D.Nmax
      (fun n hn => (hb n (List.mem_filter.1 hn).1).2.1) F, Vt_eq D Tt Pt]
  simp only [Ut_eq D Tt Pt hb, mul_list_sum, list_sum_mul]
  congr 1
  refine List.map_congr_left fun n2 _ => ?_
  rw [List.filter_filter]
  have hfilt : (D.ns.filter fun n => n.2.1 == n2 && n.1 == n1) =
      D.ns.filter fun n => n.1 == n1 && n.2.1 == n2 :=
    List.filter_congr fun n _ => Bool.and_comm _ _
  rw [hfilt]
  congr 1
  refine List.map_congr_left fun n hn => ?_
  have h12 := (List.mem_filter.1 hn).2
  simp only [Bool.and_eq_true, beq_iff_eq] at h12
  simp only [hF, ← h12.1, ← h12.2]
  push_cast
  ring

end HData

/-! ### The bridge to `hCoef` -/

/-- An exponent triple as a function on `Fin 3`. -/
def ofTriple (n : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![n.1, n.2.1, n.2.2]

/-- The action exponent of a row as a triple. -/
def tripleExp (e : (Mon × Mon) × ℤ) : ℕ × ℕ × ℕ :=
  (e.1.1.1 + e.1.2.1, e.1.1.2.1 + e.1.2.2.1, e.1.1.2.2 + e.1.2.2.2)

theorem ofTriple_tripleExp (e : (Mon × Mon) × ℤ) : ofTriple (tripleExp e) = rowExp e := by
  funext j; fin_cases j <;> rfl

theorem ofTriple_injective : Function.Injective ofTriple := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [ofTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem gbQ_eq_prod (n m : ℕ) : gbQ n m = ∏ i ∈ Finset.range m, (((n : ℚ) / 2 - i) / (i + 1)) := by
  induction m with
  | zero => simp [gbQ]
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp [gbQ, List.range_succ, List.prod_append]

/-- `gbQ n m = binom(n/2, m)`. -/
theorem gbQ_eq_gbinom (n m : ℕ) : ((gbQ n m : ℚ) : ℝ) = gbinom ((n : ℝ) / 2) m := by
  rw [show ((n : ℝ) / 2) = (((n : ℚ) / 2 : ℚ) : ℝ) by push_cast; ring, gbinom_ratCast, gbQ_eq_prod]
  congr 1
  rw [Finset.prod_div_distrib]
  congr 1
  exact_mod_cast Finset.prod_range_add_one_eq_factorial m

/-- The coefficient `c / (10^E N^{|b| + |b'|})` of a row, in `ℚ`. -/
def rowCoefQ (E N : ℕ) (e : (Mon × Mon) × ℤ) : ℚ :=
  (e.2 : ℚ) / ((10 : ℚ) ^ E * (N : ℚ) ^ (Mon.deg e.1.1 + Mon.deg e.1.2))

theorem rowCoefQ_cast (E N : ℕ) (e : (Mon × Mon) × ℤ) :
    ((rowCoefQ E N e : ℚ) : ℝ) = rowCoef E N e := by
  simp [rowCoefQ, rowCoef]

/-- The terms `(k, coef)` of the rows of action exponent `n`. -/
def tTerms (E N : ℕ) (rows : List ((Mon × Mon) × ℤ)) (n : ℕ × ℕ × ℕ) : List ((ℤ × ℤ) × ℚ) :=
  (rows.filter fun e => tripleExp e == n).map fun e => (rowMode e, rowCoefQ E N e)

/-- **`T_n` as a dense cosine series.** -/
theorem Tn_eq_denseCos (E N C : ℕ) (rows : List ((Mon × Mon) × ℤ)) (n : ℕ × ℕ × ℕ)
    (hbox : ∀ t ∈ tTerms E N rows n, inBox C t.1 = true) (φ : Fin 2 → ℝ) :
    Tn E N rows (ofTriple n) φ = denseCos C (pDense C (tTerms E N rows n)) φ := by
  rw [denseCos_pDense C _ hbox, Tn, tTerms, List.map_map]
  have hf : (rows.filter fun e => decide (rowExp e = ofTriple n)) =
      rows.filter fun e => tripleExp e == n := by
    refine List.filter_congr fun e _ => ?_
    rw [← ofTriple_tripleExp]
    by_cases h : tripleExp e = n
    · simp [h]
    · simp [h, ofTriple_injective.ne h]
  rw [hf]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, rowTrig, rowCoefQ_cast, kdot]

/-- The sorted pairs `(index, value)` of the tube centre `B_j` in the box of size `C`: `Ī_j` at
the centre and `-m_j σ` at each mode `m`. -/
def bPairs (C : ℕ) (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (j : Fin 3) : List (ℕ × ℚ) :=
  insertPair (boxIdx C (0, 0), Ibar j)
    (modes.map fun x => (boxIdx C (x.1, x.2.1), -((modeK x.1 x.2.1 j : ℤ) : ℚ) * x.2.2))
where
  /-- Insert a pair before the first pair of larger or equal index. -/
  insertPair (p : ℕ × ℚ) : List (ℕ × ℚ) → List (ℕ × ℚ)
    | [] => [p]
    | q :: qs => if p.1 ≤ q.1 then p :: q :: qs else q :: insertPair p qs

theorem sum_insertPair (f : ℕ × ℚ → ℝ) (p : ℕ × ℚ) :
    ∀ ps : List (ℕ × ℚ), ((bPairs.insertPair p ps).map f).sum = f p + (ps.map f).sum
  | [] => by simp [bPairs.insertPair]
  | q :: qs => by
    unfold bPairs.insertPair
    split_ifs
    · simp
    · simp only [List.map_cons, List.sum_cons, sum_insertPair f p qs]; ring

theorem mem_insertPair {p q : ℕ × ℚ} : ∀ {ps : List (ℕ × ℚ)}, q ∈ bPairs.insertPair p ps →
    q = p ∨ q ∈ ps
  | [], h => by simpa [bPairs.insertPair] using h
  | r :: rs, h => by
    unfold bPairs.insertPair at h
    split_ifs at h
    · simpa using h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases mem_insertPair h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem r h)

/-- **N6's tube centre as a dense cosine series**, given the kernel checks: the modes lie in the
box and the pairs are strictly sorted. -/
theorem tubeCenter_eq_denseCos (C : ℕ) (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (j : Fin 3)
    (hbox : ∀ x ∈ modes, inBox C (x.1, x.2.1) = true)
    (hinc : incFrom 0 (bPairs C modes Ibar j) = true)
    (φ : Fin 2 → ℝ) :
    tubeCenter modes Ibar j φ =
      denseCos C (scatter ((2 * C + 1) * (2 * C + 1)) 0 (bPairs C modes Ibar j)) φ := by
  have hlt : ∀ p ∈ bPairs C modes Ibar j, p.1 < (2 * C + 1) * (2 * C + 1) := by
    intro p hp
    rcases mem_insertPair hp with rfl | hp
    · exact boxIdx_lt (by simp [inBox])
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      exact boxIdx_lt (hbox x hx)
  rw [denseCos_scatter C _ hinc hlt, bPairs, sum_insertPair, tubeCenter, List.map_map]
  simp only [boxKey_boxIdx (show inBox C (0, 0) = true by simp [inBox]), kdot]
  simp only [Int.cast_zero, zero_mul, add_zero, Real.cos_zero, mul_one]
  congr 1
  congr 1
  refine List.map_congr_left fun x hx => ?_
  simp only [Function.comp_apply, boxKey_boxIdx (hbox x hx)]
  push_cast
  ring

theorem neg_list_sum {α : Type*} (l : List α) (f : α → ℝ) :
    -(l.map f).sum = (l.map fun x => -f x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, neg_add, ih]

/-- A lower bound of the tube centre: `B_j ≥ Ī_j - Σ |m_j σ|`. -/
theorem tubeCenter_ge (modes : List (ℤ × ℤ × ℚ)) (Ibar : Fin 3 → ℚ) (j : Fin 3) (φ : Fin 2 → ℝ) :
    ((Ibar j - (modes.map fun x => |((modeK x.1 x.2.1 j : ℤ) : ℚ) * x.2.2|).sum : ℚ) : ℝ) ≤
      tubeCenter modes Ibar j φ := by
  rw [tubeCenter, Rat.cast_sub, Rat.cast_list_sum, List.map_map, sub_eq_add_neg, neg_list_sum]
  refine add_le_add le_rfl (List.sum_le_sum fun x _ => ?_)
  simp only [Function.comp_apply, Rat.cast_abs, Rat.cast_mul, Rat.cast_intCast]
  have hc := Real.abs_cos_le_one (x.1 * φ 0 + x.2.1 * φ 1)
  have := neg_abs_le ((-((modeK x.1 x.2.1 j : ℤ) : ℝ) * (x.2.2 : ℝ)) *
    Real.cos (x.1 * φ 0 + x.2.1 * φ 1))
  rw [abs_mul, abs_mul (-((modeK x.1 x.2.1 j : ℤ) : ℝ)), abs_neg] at this
  have h2 : |((modeK x.1 x.2.1 j : ℤ) : ℝ)| * |(x.2.2 : ℝ)| * |Real.cos (x.1 * φ 0 + x.2.1 * φ 1)| ≤
      |((modeK x.1 x.2.1 j : ℤ) : ℝ)| * |(x.2.2 : ℝ)| :=
    mul_le_of_le_one_right (by positivity) hc
  rw [abs_mul]
  linarith

/-- **The bridge** (N7's target (2), for an arbitrary `D`): with the data equalities as hypotheses,
the Horner sum `D.Ht D.Tt D.Pt m` is N5a's Taylor coefficient `hCoef E N rows B m`. -/
theorem HData.Ht_eq_hCoef (D : HData) (E N : ℕ) (rows : List ((Mon × Mon) × ℤ))
    (B : (Fin 2 → ℝ) → Fin 3 → ℝ) (hnd : D.ns.Nodup)
    (hb : ∀ n ∈ D.ns, n.1 ≤ D.Nmax ∧ n.2.1 ≤ D.Nmax ∧ n.2.2 ≤ D.Nmax)
    (hT : ∀ n ∈ D.ns, D.Tt n = Tn E N rows (ofTriple n))
    (hB : ∀ j : Fin 3, D.Bt j = fun φ => B φ j) (hpos : ∀ φ j, 0 < B φ j)
    (hns : ∀ e ∈ rows, tripleExp e ∈ D.ns) (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    D.Ht D.Tt D.Pt m φ = hCoef E N rows B (ofTriple m) φ := by
  rw [HData.Ht_eq_sum D D.Tt D.Pt hnd hb]
  set f : (Fin 3 → ℕ) → ℝ := fun n => Tn E N rows n φ *
    ∏ j, gbinom (halfExp n j) (ofTriple m j) * B φ j ^ (halfExp n j - ofTriple m j) with hf
  have hterm : ∀ n ∈ D.ns, ((gbQ n.1 m.1 * gbQ n.2.1 m.2.1 * gbQ n.2.2 m.2.2 : ℚ) : ℝ) *
      (D.Tt n φ * D.Pt 0 ((n.1 : ℤ) - 2 * m.1) φ * D.Pt 1 ((n.2.1 : ℤ) - 2 * m.2.1) φ *
        D.Pt 2 ((n.2.2 : ℤ) - 2 * m.2.2) φ) = f (ofTriple n) := by
    intro n hn
    have hP : ∀ (j : Fin 3) (a b : ℕ), D.Pt j ((a : ℤ) - 2 * b) φ = B φ j ^ ((a : ℝ) / 2 - b) := by
      intro j a b
      rw [HData.Pt, sqrtPow, hB j, rpow_half_sub (hpos φ j)]
    have h0 := hP 0
    have h1 := hP 1
    have h2 := hP 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
    rw [hT n hn, h0, h1, h2, hf]
    simp only [Fin.prod_univ_three, halfExp, ofTriple, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Rat.cast_mul, gbQ_eq_gbinom]
    ring
  rw [List.map_congr_left hterm, show (fun a => f (ofTriple a)) = f ∘ ofTriple from rfl,
    ← List.map_map, ← List.sum_toFinset _
    ((List.nodup_map_iff ofTriple_injective).2 hnd), hCoef]
  symm
  refine Finset.sum_subset (fun n hn => ?_) (fun n _ hn => ?_)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hn)
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨tripleExp e, hns e he, ofTriple_tripleExp e⟩)
  · have hT0 : Tn E N rows n φ = 0 := by
      rw [Tn, List.filter_eq_nil_iff.2 fun e he h => hn (List.mem_toFinset.2
        (List.mem_map.2 ⟨e, he, by simpa using h⟩))]
      simp
    simp [hT0]

end KAM.EffectiveStability.Tube

end
