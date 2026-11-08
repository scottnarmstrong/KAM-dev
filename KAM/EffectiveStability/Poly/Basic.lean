/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import KAM.EffectiveStability.Poly.Coeff
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Basic
public import KAM.Frozen.Planetary.Defs.OscillatorAction

/-!
# Cartesian polynomials with exact coefficients (track B, B2-POLY, B3-COEF): algebra

A kernel-computable polynomial type for Cartesian phase space `(q, p)`. A monomial is
`c · ∏ q_i^(a i) · ∏ p_i^(b i)` with exponent lists padded by zeros; `n` enters only through
evaluation `CartPoly.cartEval` in a commutative `ℚ`-algebra (`ℝ`, `ℂ`), which ignores exponents
at indices `≥ n`.

* `CartPoly.cartAdd/cartNeg/cartSub/cartSmul/cartMul/cartConst/cartQVar/cartPVar/cartAction` and
  their evaluation lemmas;
* `CartPoly.cartNormalize` (merge equal exponent keys, drop zero coefficients),
  `cartEval_normalize`;
* `CartPoly.cartEqCheck` and `cartEval_eq_of_eqCheck` (soundness of the kernel-computable identity
  checker);
* `CartFits n P`: exponents vanish at indices `≥ n` (typing data for derivative and bracket
  statements);
* `CartPoly.eval_ofReal`: reality of the evaluation on real points.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- A monomial `c · ∏ q_i^(a i) · ∏ p_i^(b i)`; exponent lists are padded with zeros
(missing = 0). -/
structure CartMonoK (K : Type) where
  /-- exponents of the `q` variables -/
  a : List ℕ
  /-- exponents of the `p` variables -/
  b : List ℕ
  /-- the exact coefficient -/
  c : K
  deriving DecidableEq

/-- A finite sum of monomials (not necessarily normalized), with coefficients in `K`. -/
abbrev CartPolyK (K : Type) := List (CartMonoK K)

/-- Monomials with exact rational coefficients. -/
abbrev CartMono := CartMonoK ℚ

/-- A finite sum of monomials with exact rational coefficients (the original layer). -/
abbrev CartPoly := CartPolyK ℚ

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

namespace CartMonoK

variable {K : Type} [CertCoeff K] {R : Type*} [CommRing R] {n : ℕ}

/-- The monomial part `∏ i, q_i^(a i) p_i^(b i)` of an evaluation. -/
def powProd (a b : List ℕ) (z : (Fin n → R) × (Fin n → R)) : R :=
  ∏ i : Fin n, z.1 i ^ a.getD i 0 * z.2 i ^ b.getD i 0

/-- Evaluation of a monomial at `z = (q, p)`. -/
def cartMonoEval [Algebra K R] (m : CartMonoK K) (z : (Fin n → R) × (Fin n → R)) : R :=
  algebraMap K R m.c * powProd m.a m.b z

/-- Product of two monomials. -/
def cartMonoMul (m m' : CartMonoK K) : CartMonoK K :=
  ⟨addPad m.a m'.a, addPad m.b m'.b, m.c * m'.c⟩

/-- Trim trailing zeros of both exponent lists. -/
def cartMonoTrim (m : CartMonoK K) : CartMonoK K := ⟨trimExp m.a, trimExp m.b, m.c⟩

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

variable [Algebra K R] in
theorem cartMonoEval_mul (m m' : CartMonoK K) (z : (Fin n → R) × (Fin n → R)) :
    (m.cartMonoMul m').cartMonoEval z = m.cartMonoEval z * m'.cartMonoEval z := by
  simp only [cartMonoEval, cartMonoMul, powProd_addPad, map_mul]
  ring

variable [Algebra K R] in
theorem cartMonoEval_trim (m : CartMonoK K) (z : (Fin n → R) × (Fin n → R)) :
  m.cartMonoTrim.cartMonoEval z = m.cartMonoEval z := by
  simp only [cartMonoEval, cartMonoTrim]
  rw [powProd_congr (a' := m.a) (b' := m.b) (getD_trimExp _) (getD_trimExp _)]

end CartMonoK

namespace CartPoly

variable {K : Type} [CertCoeff K] {R : Type*} [CommRing R] [Algebra K R] {n : ℕ}

/-- Evaluation of a polynomial at `z = (q, p)`. -/
def cartEval (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) : R := (P.map (·.cartMonoEval z)).sum

/-- Sum (concatenation). -/
def cartAdd (P Q : CartPolyK K) : CartPolyK K := P ++ Q

/-- Negation. -/
def cartNeg (P : CartPolyK K) : CartPolyK K := P.map fun m => ⟨m.a, m.b, -m.c⟩

/-- Difference. -/
def cartSub (P Q : CartPolyK K) : CartPolyK K := cartAdd P (cartNeg Q)

/-- Scalar multiple by a coefficient. -/
def cartSmul (r : K) (P : CartPolyK K) : CartPolyK K := P.map fun m => ⟨m.a, m.b, r * m.c⟩

/-- Product (pairwise products of monomials). -/
def cartMul (P Q : CartPolyK K) : CartPolyK K := P.flatMap fun m => Q.map (CartMonoK.cartMonoMul m)

/-- A constant. -/
def cartConst (r : K) : CartPolyK K := [⟨[], [], r⟩]

/-- The coordinate `q_i`. -/
def cartQVar (i : ℕ) : CartPolyK K := [⟨unitExp i 1, [], 1⟩]

/-- The coordinate `p_i`. -/
def cartPVar (i : ℕ) : CartPolyK K := [⟨[], unitExp i 1, 1⟩]

/-- The cartAction `q_j² / 2 + p_j² / 2` (the polynomial of `KAM.Planetary.oscillatorAction`). -/
def cartAction (j : ℕ) : CartPolyK K := [⟨unitExp j 2, [], ratCoeff (1 / 2)⟩,
    ⟨[], unitExp j 2, ratCoeff (1 / 2)⟩]

@[simp] theorem cartEval_nil (z : (Fin n → R) × (Fin n → R)) : cartEval ([] : CartPolyK K) z = 0
    := by
  simp [cartEval]

@[simp] theorem cartEval_cons (m : CartMonoK K) (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (m :: P) z = m.cartMonoEval z + cartEval P z := by
  simp [cartEval]

theorem cartEval_add (P Q : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartAdd P Q) z = cartEval P z + cartEval Q z := by
  simp [cartAdd, cartEval]

theorem cartEval_neg (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) : cartEval (cartNeg P) z =
  -cartEval P z := by
  induction P with
  | nil => simp [cartNeg]
  | cons m P ih =>
    simp only [cartNeg, List.map_cons, cartEval_cons] at ih ⊢
    rw [ih]; simp [CartMonoK.cartMonoEval]; ring

theorem cartEval_sub (P Q : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartSub P Q) z = cartEval P z - cartEval Q z := by
  simp [cartSub, cartEval_add, cartEval_neg, sub_eq_add_neg]

theorem cartEval_smul (r : K) (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartSmul r P) z = algebraMap K R r * cartEval P z := by
  induction P with
  | nil => simp [cartSmul]
  | cons m P ih =>
    simp only [cartSmul, List.map_cons, cartEval_cons] at ih ⊢
    rw [ih]; simp [CartMonoK.cartMonoEval]; ring

theorem cartEval_mul_mono (m : CartMonoK K) (Q : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (Q.map (CartMonoK.cartMonoMul m)) z = m.cartMonoEval z * cartEval Q z := by
  induction Q with
  | nil => simp
  | cons m' Q ih => simp only [List.map_cons, cartEval_cons, CartMonoK.cartMonoEval_mul, ih]; ring

theorem cartEval_mul (P Q : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartMul P Q) z = cartEval P z * cartEval Q z := by
  induction P with
  | nil => simp [cartMul]
  | cons m P ih =>
    have : cartMul (m :: P) Q = Q.map (CartMonoK.cartMonoMul m) ++ cartMul P Q := by simp [cartMul]
    rw [this, ← cartAdd, cartEval_add, cartEval_mul_mono, ih, cartEval_cons]; ring

theorem cartEval_const (r : K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartConst r) z = algebraMap K R r := by
  simp [cartConst, CartMonoK.cartMonoEval, CartMonoK.powProd]

omit [Algebra K R] in
theorem powProd_unit_q (j e : ℕ) (hj : j < n) (z : (Fin n → R) × (Fin n → R)) :
    CartMonoK.powProd (unitExp j e) [] z = z.1 ⟨j, hj⟩ ^ e := by
  unfold CartMonoK.powProd
  rw [Finset.prod_eq_single ⟨j, hj⟩]
  · simp only [getD_unitExp, List.getD_nil]; simp
  · intro k _ hk
    have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    simp only [getD_unitExp, List.getD_nil, this, ite_false]; simp
  · simp

omit [Algebra K R] in
theorem powProd_unit_p (j e : ℕ) (hj : j < n) (z : (Fin n → R) × (Fin n → R)) :
    CartMonoK.powProd [] (unitExp j e) z = z.2 ⟨j, hj⟩ ^ e := by
  unfold CartMonoK.powProd
  rw [Finset.prod_eq_single ⟨j, hj⟩]
  · simp only [getD_unitExp, List.getD_nil]; simp
  · intro k _ hk
    have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    simp only [getD_unitExp, List.getD_nil, this, ite_false]; simp
  · simp

theorem cartEval_qVar (i : Fin n) (z : (Fin n → R) × (Fin n → R)) : cartEval (cartQVar (K := K) i)
    z = z.1 i
  := by
  simp [cartQVar, CartMonoK.cartMonoEval, powProd_unit_q _ _ i.2]

theorem cartEval_pVar (i : Fin n) (z : (Fin n → R) × (Fin n → R)) : cartEval (cartPVar (K := K) i)
    z = z.2 i
  := by
  simp [cartPVar, CartMonoK.cartMonoEval, powProd_unit_p _ _ i.2]

theorem cartEval_action_eq (j : Fin n) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartAction (K := K) j) z = algebraMap K R (ratCoeff (1 / 2)) * (z.1 j ^ 2 + z.2 j ^
      2) := by
  have h1 : CartMonoK.powProd (unitExp j 2) [] z = z.1 j ^ 2 := powProd_unit_q _ _ j.2 z
  have h2 : CartMonoK.powProd [] (unitExp j 2) z = z.2 j ^ 2 := powProd_unit_p _ _ j.2 z
  simp only [cartAction, cartEval_cons, cartEval_nil, CartMonoK.cartMonoEval, h1, h2]
  ring

/-- `cartEval_action`: the polynomial `cartAction j` is the oscillator cartAction. -/
theorem cartEval_action [Algebra K ℝ] (j : Fin n) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval (cartAction (K := K) j) z = KAM.Planetary.oscillatorAction z.2 z.1 j := by
  rw [cartEval_action_eq, algebraMap_ratCoeff]
  simp only [KAM.Planetary.oscillatorAction]
  push_cast
  ring

/-! ### Normalization and the identity checker -/

/-- Insert a monomial, merging with an existing monomial with the same exponent lists. -/
def cartInsertMono (m : CartMonoK K) : CartPolyK K → CartPolyK K
  | [] => [m]
  | m' :: P =>
    if m'.a = m.a ∧ m'.b = m.b then ⟨m'.a, m'.b, m'.c + m.c⟩ :: P else m' :: cartInsertMono m P

theorem cartEval_insertMono (m : CartMonoK K) (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartInsertMono m P) z = m.cartMonoEval z + cartEval P z := by
  induction P with
  | nil => simp [cartInsertMono]
  | cons m' P ih =>
    unfold cartInsertMono
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [cartEval_cons, CartMonoK.cartMonoEval, h1, h2, map_add]
      ring
    · rw [cartEval_cons, ih, cartEval_cons]; ring

/-- Merge a list of monomials by exponent key. -/
def cartMerge (P : CartPolyK K) : CartPolyK K := P.foldr cartInsertMono []

theorem cartEval_merge (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartMerge P) z = cartEval P z := by
  induction P with
  | nil => simp [cartMerge]
  | cons m P ih =>
    have : cartMerge (m :: P) = cartInsertMono m (cartMerge P) := rfl
    rw [this, cartEval_insertMono, ih, cartEval_cons]

theorem cartEval_trimmap (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (P.map CartMonoK.cartMonoTrim) z = cartEval P z := by
  induction P with
  | nil => simp
  | cons m P ih => simp only [List.map_cons, cartEval_cons, CartMonoK.cartMonoEval_trim, ih]

theorem cartEval_filter_ne (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (P.filter fun m => decide (m.c ≠ 0)) z = cartEval P z := by
  induction P with
  | nil => simp
  | cons m P ih =>
    by_cases h : m.c = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, cartEval_cons]; simp [CartMonoK.cartMonoEval,
      h]
    · rw [List.filter_cons_of_pos (by simpa using h), cartEval_cons, cartEval_cons, ih]

/-- Normal form: trim trailing zeros, cartMerge equal exponent keys, drop zero coefficients. -/
def cartNormalize (P : CartPolyK K) : CartPolyK K :=
  (cartMerge (P.map CartMonoK.cartMonoTrim)).filter fun m => decide (m.c ≠ 0)

theorem cartEval_normalize (P : CartPolyK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartNormalize P) z = cartEval P z := by
  rw [cartNormalize, cartEval_filter_ne, cartEval_merge, cartEval_trimmap]

/-- The identity checker: `cartNormalize (P - Q) = []`. -/
def cartEqCheck (P Q : CartPolyK K) : Bool := (cartNormalize (cartSub P Q)).isEmpty

theorem cartEval_eq_of_eqCheck {P Q : CartPolyK K} (h : cartEqCheck P Q = true)
    (z : (Fin n → R) × (Fin n → R)) : cartEval P z = cartEval Q z := by
  have h0 : cartNormalize (cartSub P Q) = [] := by simpa [cartEqCheck] using h
  have := cartEval_normalize (cartSub P Q) z
  rw [h0, cartEval_sub] at this
  exact sub_eq_zero.1 this.symm

/-! ### Typing data -/

/-- `CartFits n P`: all exponents at indices `≥ n` vanish, so that `cartEval` loses nothing. -/
def CartFits (n : ℕ) (P : CartPolyK K) : Prop :=
  ∀ m ∈ P, ∀ k, n ≤ k → m.a.getD k 0 = 0 ∧ m.b.getD k 0 = 0

omit [CertCoeff K] in
theorem cartFits_nil (n : ℕ) : CartFits n ([] : CartPolyK K) := by simp [CartFits]

omit [CertCoeff K] in
theorem cartFits_add {P Q : CartPolyK K} (hP : CartFits n P) (hQ : CartFits n Q) : CartFits n
    (cartAdd
  P Q) := by
  intro m hm k hk
  rcases List.mem_append.1 hm with h | h
  exacts [hP m h k hk, hQ m h k hk]

theorem cartFits_neg {P : CartPolyK K} (hP : CartFits n P) : CartFits n (cartNeg P) := by
  intro m hm k hk
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  exact hP m' hm' k hk

theorem cartFits_sub {P Q : CartPolyK K} (hP : CartFits n P) (hQ : CartFits n Q) : CartFits n
    (cartSub
  P Q) :=
  cartFits_add hP (cartFits_neg hQ)

theorem cartFits_smul (r : K) {P : CartPolyK K} (hP : CartFits n P) : CartFits n (cartSmul r P) :=
    by
  intro m hm k hk
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  exact hP m' hm' k hk

theorem cartFits_mul {P Q : CartPolyK K} (hP : CartFits n P) (hQ : CartFits n Q) : CartFits n
    (cartMul
  P Q) := by
  intro m hm k hk
  obtain ⟨m1, hm1, hm⟩ := List.mem_flatMap.1 hm
  obtain ⟨m2, hm2, rfl⟩ := List.mem_map.1 hm
  have h1 := hP m1 hm1 k hk
  have h2 := hQ m2 hm2 k hk
  simp only [CartMonoK.cartMonoMul, getD_addPad, h1.1, h1.2, h2.1, h2.2, and_self]

omit [CertCoeff K] in
theorem cartFits_const (r : K) : CartFits n (cartConst r) := by
  intro m hm k _
  obtain rfl : m = ⟨[], [], r⟩ := List.mem_singleton.1 hm
  exact ⟨List.getD_nil, List.getD_nil⟩

theorem cartFits_qVar {j : ℕ} (hj : j < n) : CartFits n (cartQVar (K := K) j) := by
  intro m hm k hk
  obtain rfl : m = ⟨unitExp j 1, [], 1⟩ := List.mem_singleton.1 hm
  have : k ≠ j := by omega
  exact ⟨by simp only [getD_unitExp, this, ite_false], List.getD_nil⟩

theorem cartFits_pVar {j : ℕ} (hj : j < n) : CartFits n (cartPVar (K := K) j) := by
  intro m hm k hk
  obtain rfl : m = ⟨[], unitExp j 1, 1⟩ := List.mem_singleton.1 hm
  have : k ≠ j := by omega
  exact ⟨List.getD_nil, by simp only [getD_unitExp, this, ite_false]⟩

theorem cartFits_action {j : ℕ} (hj : j < n) : CartFits n (cartAction (K := K) j) := by
  intro m hm k hk
  have : k ≠ j := by omega
  simp only [CartPoly.cartAction, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨by simp only [getD_unitExp, this, ite_false], List.getD_nil⟩
  · exact ⟨List.getD_nil, by simp only [getD_unitExp, this, ite_false]⟩

/-! ### Reality -/

/-- A polynomial with coefficients in `K` evaluates, at a real point viewed in `ℂ`, to the
(complexified) real value. -/
theorem cartEval_ofReal [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] (P : CartPolyK K)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval P ((fun i => ((x.1 i : ℝ) : ℂ), fun i => ((x.2 i : ℝ) : ℂ)) :
      (Fin n → ℂ) × (Fin n → ℂ)) = (((cartEval P x : ℝ)) : ℂ) := by
  induction P with
  | nil => simp
  | cons m P ih =>
    rw [cartEval_cons, cartEval_cons, ih]
    push_cast
    congr 1
    simp only [CartMonoK.cartMonoEval, CartMonoK.powProd, IsScalarTower.algebraMap_apply K ℝ ℂ]
    push_cast
    rfl

end CartPoly

end KAM.EffectiveStability
