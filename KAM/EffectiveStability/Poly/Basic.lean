/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Basic
public import KAM.Frozen.Planetary.Defs.OscillatorAction

/-!
# Cartesian polynomials with exact `ℚ` coefficients (track B, B2-POLY): algebra

A kernel-computable polynomial type for Cartesian phase space `(q, p)`. A monomial is
`c · ∏ q_i^(a i) · ∏ p_i^(b i)` with exponent lists padded by zeros; `n` enters only through
evaluation `CartPoly.eval` in a commutative `ℚ`-algebra (`ℝ`, `ℂ`), which ignores exponents
at indices `≥ n`.

* `CartPoly.add/neg/sub/smul/mul/const/qVar/pVar/action` and their evaluation lemmas;
* `CartPoly.normalize` (merge equal exponent keys, drop zero coefficients), `eval_normalize`;
* `CartPoly.eqCheck` and `eval_eq_of_eqCheck` (soundness of the kernel-computable identity checker);
* `CartPoly.Fits n P`: exponents vanish at indices `≥ n` (typing data for derivative and bracket
  statements);
* `CartPoly.eval_ofReal`: reality of the evaluation on real points.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- A monomial `c · ∏ q_i^(a i) · ∏ p_i^(b i)`; exponent lists are padded with zeros
(missing = 0). -/
structure CartMono where
  /-- exponents of the `q` variables -/
  a : List ℕ
  /-- exponents of the `p` variables -/
  b : List ℕ
  /-- the exact rational coefficient -/
  c : ℚ
  deriving DecidableEq

/-- A finite sum of monomials (not necessarily normalized). -/
abbrev CartPoly := List CartMono

/-- Pointwise sum of exponent lists, padding the shorter list with zeros. -/
def addPad : List ℕ → List ℕ → List ℕ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addPad as bs

theorem getD_addPad (as bs : List ℕ) (k : ℕ) :
    (addPad as bs).getD k 0 = as.getD k 0 + bs.getD k 0 := by
  induction as generalizing bs k with
  | nil => simp [addPad]
  | cons a as ih =>
    cases bs with
    | nil => simp [addPad]
    | cons b bs =>
      cases k with
      | zero => simp [addPad]
      | succ k => simpa [addPad] using ih bs k

/-- The exponent list with a single entry `e` at index `j`. -/
def unitExp (j e : ℕ) : List ℕ := List.replicate j 0 ++ [e]

theorem getD_unitExp (j e k : ℕ) : (unitExp j e).getD k 0 = if k = j then e else 0 := by
  unfold unitExp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases hk : k < j
  · simp [hk, Nat.ne_of_lt hk]
  · by_cases hkj : k = j
    · subst hkj; simp
    · have : 0 < k - j := by omega
      simp [hk, hkj, List.getElem?_eq_none_iff.2 (by simp; omega : [e].length ≤ k - j)]

/-- Remove trailing zeros of an exponent list. -/
def trimExp : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x = 0 ∧ trimExp xs = [] then [] else x :: trimExp xs

theorem getD_trimExp (l : List ℕ) (k : ℕ) : (trimExp l).getD k 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [trimExp]
  | cons x xs ih =>
    by_cases h : x = 0 ∧ trimExp xs = []
    · have h1 : ∀ k, xs.getD k 0 = 0 := fun k => by simpa [h.2] using (ih k).symm
      have ht : trimExp (x :: xs) = [] := by simp [trimExp, h]
      rw [ht]
      cases k with
      | zero => simp [h.1]
      | succ k => simp only [List.getD_nil, List.getD_cons_succ, h1 k]
    · cases k with
      | zero => simp [trimExp, h]
      | succ k => simp only [trimExp, h, ite_false]; simpa using ih k

namespace CartMono

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The monomial part `∏ i, q_i^(a i) p_i^(b i)` of an evaluation. -/
def powProd (a b : List ℕ) (z : (Fin n → R) × (Fin n → R)) : R :=
  ∏ i : Fin n, z.1 i ^ a.getD i 0 * z.2 i ^ b.getD i 0

/-- Evaluation of a monomial at `z = (q, p)`. -/
def eval [Algebra ℚ R] (m : CartMono) (z : (Fin n → R) × (Fin n → R)) : R :=
  algebraMap ℚ R m.c * powProd m.a m.b z

/-- Product of two monomials. -/
def mul (m m' : CartMono) : CartMono := ⟨addPad m.a m'.a, addPad m.b m'.b, m.c * m'.c⟩

/-- Trim trailing zeros of both exponent lists. -/
def trim (m : CartMono) : CartMono := ⟨trimExp m.a, trimExp m.b, m.c⟩

theorem powProd_congr {a a' b b' : List ℕ} (ha : ∀ k, a.getD k 0 = a'.getD k 0)
    (hb : ∀ k, b.getD k 0 = b'.getD k 0) (z : (Fin n → R) × (Fin n → R)) :
    powProd a b z = powProd a' b' z := by
  unfold powProd
  exact Finset.prod_congr rfl fun i _ => by rw [ha, hb]

theorem powProd_addPad (a a' b b' : List ℕ) (z : (Fin n → R) × (Fin n → R)) :
    powProd (addPad a a') (addPad b b') z = powProd a b z * powProd a' b' z := by
  unfold powProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [getD_addPad, pow_add]
  ring

variable [Algebra ℚ R] in
theorem eval_mul (m m' : CartMono) (z : (Fin n → R) × (Fin n → R)) :
    (m.mul m').eval z = m.eval z * m'.eval z := by
  simp only [eval, mul, powProd_addPad, map_mul]
  ring

variable [Algebra ℚ R] in
theorem eval_trim (m : CartMono) (z : (Fin n → R) × (Fin n → R)) : m.trim.eval z = m.eval z := by
  simp only [eval, trim]
  rw [powProd_congr (a' := m.a) (b' := m.b) (getD_trimExp _) (getD_trimExp _)]

end CartMono

namespace CartPoly

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

/-- Evaluation of a polynomial at `z = (q, p)`. -/
def eval (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) : R := (P.map (·.eval z)).sum

/-- Sum (concatenation). -/
def add (P Q : CartPoly) : CartPoly := P ++ Q

/-- Negation. -/
def neg (P : CartPoly) : CartPoly := P.map fun m => ⟨m.a, m.b, -m.c⟩

/-- Difference. -/
def sub (P Q : CartPoly) : CartPoly := add P (neg Q)

/-- Scalar multiple by a rational. -/
def smul (r : ℚ) (P : CartPoly) : CartPoly := P.map fun m => ⟨m.a, m.b, r * m.c⟩

/-- Product (pairwise products of monomials). -/
def mul (P Q : CartPoly) : CartPoly := P.flatMap fun m => Q.map (CartMono.mul m)

/-- A constant. -/
def const (r : ℚ) : CartPoly := [⟨[], [], r⟩]

/-- The coordinate `q_i`. -/
def qVar (i : ℕ) : CartPoly := [⟨unitExp i 1, [], 1⟩]

/-- The coordinate `p_i`. -/
def pVar (i : ℕ) : CartPoly := [⟨[], unitExp i 1, 1⟩]

/-- The action `q_j² / 2 + p_j² / 2` (the polynomial of `KAM.Planetary.oscillatorAction`). -/
def action (j : ℕ) : CartPoly := [⟨unitExp j 2, [], 1 / 2⟩, ⟨[], unitExp j 2, 1 / 2⟩]

@[simp] theorem eval_nil (z : (Fin n → R) × (Fin n → R)) : eval ([] : CartPoly) z = 0 := by
  simp [eval]

@[simp] theorem eval_cons (m : CartMono) (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (m :: P) z = m.eval z + eval P z := by
  simp [eval]

theorem eval_add (P Q : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (add P Q) z = eval P z + eval Q z := by
  simp [add, eval]

theorem eval_neg (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) : eval (neg P) z = -eval P z := by
  induction P with
  | nil => simp [neg]
  | cons m P ih =>
    simp only [neg, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; simp [CartMono.eval]; ring

theorem eval_sub (P Q : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (sub P Q) z = eval P z - eval Q z := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_smul (r : ℚ) (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (smul r P) z = algebraMap ℚ R r * eval P z := by
  induction P with
  | nil => simp [smul]
  | cons m P ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; simp [CartMono.eval]; ring

theorem eval_mul_mono (m : CartMono) (Q : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (Q.map (CartMono.mul m)) z = m.eval z * eval Q z := by
  induction Q with
  | nil => simp
  | cons m' Q ih => simp only [List.map_cons, eval_cons, CartMono.eval_mul, ih]; ring

theorem eval_mul (P Q : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (mul P Q) z = eval P z * eval Q z := by
  induction P with
  | nil => simp [mul]
  | cons m P ih =>
    have : mul (m :: P) Q = Q.map (CartMono.mul m) ++ mul P Q := by simp [mul]
    rw [this, ← add, eval_add, eval_mul_mono, ih, eval_cons]; ring

theorem eval_const (r : ℚ) (z : (Fin n → R) × (Fin n → R)) :
    eval (const r) z = algebraMap ℚ R r := by
  simp [const, CartMono.eval, CartMono.powProd]

omit [Algebra ℚ R] in
theorem powProd_unit_q (j e : ℕ) (hj : j < n) (z : (Fin n → R) × (Fin n → R)) :
    CartMono.powProd (unitExp j e) [] z = z.1 ⟨j, hj⟩ ^ e := by
  unfold CartMono.powProd
  rw [Finset.prod_eq_single ⟨j, hj⟩]
  · simp only [getD_unitExp, List.getD_nil]; simp
  · intro k _ hk
    have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    simp only [getD_unitExp, List.getD_nil, this, ite_false]; simp
  · simp

omit [Algebra ℚ R] in
theorem powProd_unit_p (j e : ℕ) (hj : j < n) (z : (Fin n → R) × (Fin n → R)) :
    CartMono.powProd [] (unitExp j e) z = z.2 ⟨j, hj⟩ ^ e := by
  unfold CartMono.powProd
  rw [Finset.prod_eq_single ⟨j, hj⟩]
  · simp only [getD_unitExp, List.getD_nil]; simp
  · intro k _ hk
    have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    simp only [getD_unitExp, List.getD_nil, this, ite_false]; simp
  · simp

theorem eval_qVar (i : Fin n) (z : (Fin n → R) × (Fin n → R)) : eval (qVar i) z = z.1 i := by
  simp [qVar, CartMono.eval, powProd_unit_q _ _ i.2]

theorem eval_pVar (i : Fin n) (z : (Fin n → R) × (Fin n → R)) : eval (pVar i) z = z.2 i := by
  simp [pVar, CartMono.eval, powProd_unit_p _ _ i.2]

theorem eval_action_eq (j : Fin n) (z : (Fin n → R) × (Fin n → R)) :
    eval (action j) z = algebraMap ℚ R (1 / 2) * (z.1 j ^ 2 + z.2 j ^ 2) := by
  have h1 : CartMono.powProd (unitExp j 2) [] z = z.1 j ^ 2 := powProd_unit_q _ _ j.2 z
  have h2 : CartMono.powProd [] (unitExp j 2) z = z.2 j ^ 2 := powProd_unit_p _ _ j.2 z
  simp only [action, eval_cons, eval_nil, CartMono.eval, h1, h2]
  ring

/-- `eval_action`: the polynomial `action j` is the oscillator action. -/
theorem eval_action (j : Fin n) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    eval (action j) z = KAM.Planetary.oscillatorAction z.2 z.1 j := by
  rw [eval_action_eq, eq_ratCast (algebraMap ℚ ℝ)]
  simp only [KAM.Planetary.oscillatorAction]
  push_cast
  ring

/-! ### Normalization and the identity checker -/

/-- Insert a monomial, merging with an existing monomial with the same exponent lists. -/
def insertMono (m : CartMono) : CartPoly → CartPoly
  | [] => [m]
  | m' :: P =>
    if m'.a = m.a ∧ m'.b = m.b then ⟨m'.a, m'.b, m'.c + m.c⟩ :: P else m' :: insertMono m P

theorem eval_insertMono (m : CartMono) (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (insertMono m P) z = m.eval z + eval P z := by
  induction P with
  | nil => simp [insertMono]
  | cons m' P ih =>
    unfold insertMono
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [eval_cons, CartMono.eval, h1, h2, map_add]
      ring
    · rw [eval_cons, ih, eval_cons]; ring

/-- Merge a list of monomials by exponent key. -/
def merge (P : CartPoly) : CartPoly := P.foldr insertMono []

theorem eval_merge (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (merge P) z = eval P z := by
  induction P with
  | nil => simp [merge]
  | cons m P ih =>
    have : merge (m :: P) = insertMono m (merge P) := rfl
    rw [this, eval_insertMono, ih, eval_cons]

theorem eval_trimmap (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (P.map CartMono.trim) z = eval P z := by
  induction P with
  | nil => simp
  | cons m P ih => simp only [List.map_cons, eval_cons, CartMono.eval_trim, ih]

theorem eval_filter_ne (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (P.filter fun m => decide (m.c ≠ 0)) z = eval P z := by
  induction P with
  | nil => simp
  | cons m P ih =>
    by_cases h : m.c = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, eval_cons]; simp [CartMono.eval, h]
    · rw [List.filter_cons_of_pos (by simpa using h), eval_cons, eval_cons, ih]

/-- Normal form: trim trailing zeros, merge equal exponent keys, drop zero coefficients. -/
def normalize (P : CartPoly) : CartPoly :=
  (merge (P.map CartMono.trim)).filter fun m => decide (m.c ≠ 0)

theorem eval_normalize (P : CartPoly) (z : (Fin n → R) × (Fin n → R)) :
    eval (normalize P) z = eval P z := by
  rw [normalize, eval_filter_ne, eval_merge, eval_trimmap]

/-- The identity checker: `normalize (P - Q) = []`. -/
def eqCheck (P Q : CartPoly) : Bool := (normalize (sub P Q)).isEmpty

theorem eval_eq_of_eqCheck {P Q : CartPoly} (h : eqCheck P Q = true)
    (z : (Fin n → R) × (Fin n → R)) : eval P z = eval Q z := by
  have h0 : normalize (sub P Q) = [] := by simpa [eqCheck] using h
  have := eval_normalize (sub P Q) z
  rw [h0, eval_sub] at this
  exact sub_eq_zero.1 this.symm

/-! ### Typing data -/

/-- `Fits n P`: all exponents at indices `≥ n` vanish, so that `eval` loses nothing. -/
def Fits (n : ℕ) (P : CartPoly) : Prop :=
  ∀ m ∈ P, ∀ k, n ≤ k → m.a.getD k 0 = 0 ∧ m.b.getD k 0 = 0

theorem Fits.nil (n : ℕ) : Fits n ([] : CartPoly) := by simp [Fits]

theorem Fits.add {P Q : CartPoly} (hP : Fits n P) (hQ : Fits n Q) : Fits n (add P Q) := by
  intro m hm k hk
  rcases List.mem_append.1 hm with h | h
  exacts [hP m h k hk, hQ m h k hk]

theorem Fits.neg {P : CartPoly} (hP : Fits n P) : Fits n (neg P) := by
  intro m hm k hk
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  exact hP m' hm' k hk

theorem Fits.sub {P Q : CartPoly} (hP : Fits n P) (hQ : Fits n Q) : Fits n (sub P Q) :=
  hP.add hQ.neg

theorem Fits.smul (r : ℚ) {P : CartPoly} (hP : Fits n P) : Fits n (smul r P) := by
  intro m hm k hk
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  exact hP m' hm' k hk

theorem Fits.mul {P Q : CartPoly} (hP : Fits n P) (hQ : Fits n Q) : Fits n (mul P Q) := by
  intro m hm k hk
  obtain ⟨m1, hm1, hm⟩ := List.mem_flatMap.1 hm
  obtain ⟨m2, hm2, rfl⟩ := List.mem_map.1 hm
  have h1 := hP m1 hm1 k hk
  have h2 := hQ m2 hm2 k hk
  simp only [CartMono.mul, getD_addPad, h1.1, h1.2, h2.1, h2.2, and_self]

theorem Fits.const (r : ℚ) : Fits n (const r) := by
  intro m hm k _
  obtain rfl : m = ⟨[], [], r⟩ := List.mem_singleton.1 hm
  exact ⟨List.getD_nil, List.getD_nil⟩

theorem Fits.qVar {j : ℕ} (hj : j < n) : Fits n (qVar j) := by
  intro m hm k hk
  obtain rfl : m = ⟨unitExp j 1, [], 1⟩ := List.mem_singleton.1 hm
  have : k ≠ j := by omega
  exact ⟨by simp only [getD_unitExp, this, ite_false], List.getD_nil⟩

theorem Fits.pVar {j : ℕ} (hj : j < n) : Fits n (pVar j) := by
  intro m hm k hk
  obtain rfl : m = ⟨[], unitExp j 1, 1⟩ := List.mem_singleton.1 hm
  have : k ≠ j := by omega
  exact ⟨List.getD_nil, by simp only [getD_unitExp, this, ite_false]⟩

theorem Fits.action {j : ℕ} (hj : j < n) : Fits n (action j) := by
  intro m hm k hk
  have : k ≠ j := by omega
  simp only [CartPoly.action, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨by simp only [getD_unitExp, this, ite_false], List.getD_nil⟩
  · exact ⟨List.getD_nil, by simp only [getD_unitExp, this, ite_false]⟩

/-! ### Reality -/

/-- A polynomial with rational coefficients evaluates, at a real point viewed in `ℂ`, to the
(complexified) real value. -/
theorem eval_ofReal (P : CartPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    eval P ((fun i => ((x.1 i : ℝ) : ℂ), fun i => ((x.2 i : ℝ) : ℂ)) :
      (Fin n → ℂ) × (Fin n → ℂ)) = (((eval P x : ℝ)) : ℂ) := by
  induction P with
  | nil => simp
  | cons m P ih =>
    rw [eval_cons, eval_cons, ih]
    push_cast
    congr 1
    simp only [CartMono.eval, CartMono.powProd, eq_ratCast (algebraMap ℚ ℂ),
      eq_ratCast (algebraMap ℚ ℝ)]
    push_cast
    rfl

end CartPoly

end KAM.EffectiveStability
