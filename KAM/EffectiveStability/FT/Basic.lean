/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Fourier–Taylor polynomials (track B, B4-FT): algebra

A kernel-computable type for functions of period-one angles `φ` and actions `J`:
`ftMonoEvalG` of `⟨k, α, e, c, s⟩` is
`(2π)^e (c cos(2π k·φ) + s sin(2π k·φ)) ∏ J_i^{α_i}` (missing list entries are `0`), so
real-valuedness is structural and all data are rational.

* `FTMono`, `FTPoly`, the generic evaluation `ftEvalG` (parameterized by `cos`, `sin`, `π` and a
  bundle `FTTrig` of their functional equations) and the two instances `ftEvalR` (`Real.cos`),
  `ftEvalC` (`Complex.cos`), with `ftEvalC_ofReal`;
* `ftAdd/ftNeg/ftSub/ftSmul/ftMul/ftConst/ftJVar/ftCosMode/ftSinMode` with evaluation lemmas;
* `ftNormalize` (trim, canonical sign of `k`, merge equal `(k, α, e)` keys, drop zero terms),
  `ftEqCheck` and its soundness;
* `FTFits n P` and the Boolean checker `ftFitsCheck`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- A Fourier–Taylor monomial, meaning
`(2π)^e (c cos(2π k·φ) + s sin(2π k·φ)) ∏ J_i^{α_i}` (missing list entries are `0`). -/
structure FTMono where
  /-- the integer frequency vector `k` -/
  k : List ℤ
  /-- the action exponents `α` -/
  α : List ℕ
  /-- the power of `2π` produced by angle derivatives -/
  e : ℕ
  /-- the rational cosine coefficient -/
  c : ℚ
  /-- the rational sine coefficient -/
  s : ℚ
  deriving DecidableEq

/-- A finite sum of Fourier–Taylor monomials. -/
abbrev FTPoly := List FTMono

/-- Pointwise sum of integer lists, padding the shorter with zeros. -/
def ftAddPadZ : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: ftAddPadZ as bs

theorem ftGetD_addPadZ (as bs : List ℤ) (k : ℕ) :
    (ftAddPadZ as bs).getD k 0 = as.getD k 0 + bs.getD k 0 := by
  induction as generalizing bs k with
  | nil => simp [ftAddPadZ]
  | cons a as ih =>
    cases bs with
    | nil => simp [ftAddPadZ]
    | cons b bs =>
      cases k with
      | zero => simp [ftAddPadZ]
      | succ k => simpa [ftAddPadZ] using ih bs k

theorem ftGetD_neg (l : List ℤ) (k : ℕ) : (l.map Neg.neg).getD k 0 = -l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k

/-- Remove trailing zeros of an integer list. -/
def ftTrimZ : List ℤ → List ℤ
  | [] => []
  | x :: xs => if x = 0 ∧ ftTrimZ xs = [] then [] else x :: ftTrimZ xs

theorem ftGetD_trimZ (l : List ℤ) (k : ℕ) : (ftTrimZ l).getD k 0 = l.getD k 0 := by
  induction l generalizing k with
  | nil => simp [ftTrimZ]
  | cons x xs ih =>
    by_cases h : x = 0 ∧ ftTrimZ xs = []
    · have h1 : ∀ k, xs.getD k 0 = 0 := fun k => by simpa [h.2] using (ih k).symm
      have ht : ftTrimZ (x :: xs) = [] := by simp [ftTrimZ, h]
      rw [ht]
      cases k with
      | zero => simp [h.1]
      | succ k => simp only [List.getD_nil, List.getD_cons_succ, h1 k]
    · cases k with
      | zero => simp [ftTrimZ, h]
      | succ k => simp only [ftTrimZ, h, ite_false]; simpa using ih k

/-- Is the first nonzero entry of `k` negative? -/
def ftFirstNeg : List ℤ → Bool
  | [] => false
  | x :: xs => if x = 0 then ftFirstNeg xs else decide (x < 0)

theorem ftGetD_zero_of_length_le {α : Type*} [Zero α] (l : List α) (i : ℕ) (h : l.length ≤ i) :
    l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- A bundle of the functional equations of a cosine/sine pair. -/
structure FTTrig {𝕜 : Type*} [Field 𝕜] (cf sf : 𝕜 → 𝕜) : Prop where
  /-- `cos 0 = 1` -/
  cos_zero : cf 0 = 1
  /-- `sin 0 = 0` -/
  sin_zero : sf 0 = 0
  /-- the addition formula for cosine -/
  cos_add : ∀ a b, cf (a + b) = cf a * cf b - sf a * sf b
  /-- the addition formula for sine -/
  sin_add : ∀ a b, sf (a + b) = sf a * cf b + cf a * sf b
  /-- evenness of cosine -/
  cos_neg : ∀ a, cf (-a) = cf a
  /-- oddness of sine -/
  sin_neg : ∀ a, sf (-a) = -sf a

theorem ftTrig_real : FTTrig Real.cos Real.sin :=
  ⟨Real.cos_zero, Real.sin_zero, Real.cos_add, Real.sin_add, Real.cos_neg, Real.sin_neg⟩

theorem ftTrig_complex : FTTrig Complex.cos Complex.sin :=
  ⟨Complex.cos_zero, Complex.sin_zero, Complex.cos_add, Complex.sin_add, Complex.cos_neg,
    Complex.sin_neg⟩

section Generic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {n : ℕ}

/-- The phase `k · φ = ∑ k_i φ_i`. -/
def ftPhase (k : List ℤ) (φ : Fin n → 𝕜) : 𝕜 := ∑ i : Fin n, ((k.getD i 0 : ℤ) : 𝕜) * φ i

/-- The action monomial `∏ J_i^{α_i}`. -/
def ftJProd (α : List ℕ) (J : Fin n → 𝕜) : 𝕜 := ∏ i : Fin n, J i ^ α.getD i 0

/-- Generic evaluation of a monomial; `p` stands for `π`. -/
def ftMonoEvalG (cf sf : 𝕜 → 𝕜) (p : 𝕜) (m : FTMono) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) : 𝕜 :=
  (2 * p) ^ m.e * ((m.c : 𝕜) * cf (2 * p * ftPhase m.k z.1) +
    (m.s : 𝕜) * sf (2 * p * ftPhase m.k z.1)) * ftJProd m.α z.2

/-- Generic evaluation of a Fourier–Taylor polynomial. -/
def ftEvalG (cf sf : 𝕜 → 𝕜) (p : 𝕜) (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) : 𝕜 :=
  (P.map fun m => ftMonoEvalG cf sf p m z).sum

variable (cf sf : 𝕜 → 𝕜) (p : 𝕜)

omit [CharZero 𝕜] in
@[simp] theorem ftEvalG_nil (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p ([] : FTPoly) z = 0 := by simp [ftEvalG]

omit [CharZero 𝕜] in
@[simp] theorem ftEvalG_cons (m : FTMono) (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (m :: P) z = ftMonoEvalG cf sf p m z + ftEvalG cf sf p P z := by
  simp [ftEvalG]

omit [CharZero 𝕜] in
theorem ftEvalG_append (P Q : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (P ++ Q) z = ftEvalG cf sf p P z + ftEvalG cf sf p Q z := by
  simp [ftEvalG]

/-- Sum (concatenation). -/
def ftAdd (P Q : FTPoly) : FTPoly := P ++ Q

/-- Negation. -/
def ftNeg (P : FTPoly) : FTPoly := P.map fun m => ⟨m.k, m.α, m.e, -m.c, -m.s⟩

/-- Difference. -/
def ftSub (P Q : FTPoly) : FTPoly := ftAdd P (ftNeg Q)

/-- Scalar multiple by a rational. -/
def ftSmul (r : ℚ) (P : FTPoly) : FTPoly := P.map fun m => ⟨m.k, m.α, m.e, r * m.c, r * m.s⟩

/-- The constant `r`. -/
def ftConst (r : ℚ) : FTPoly := [⟨[], [], 0, r, 0⟩]

/-- The action variable `J_i`. -/
def ftJVar (i : ℕ) : FTPoly := [⟨[], unitExp i 1, 0, 1, 0⟩]

/-- The pure mode `cos(2π k·φ)`. -/
def ftCosMode (k : List ℤ) : FTPoly := [⟨k, [], 0, 1, 0⟩]

/-- The pure mode `sin(2π k·φ)`. -/
def ftSinMode (k : List ℤ) : FTPoly := [⟨k, [], 0, 0, 1⟩]

omit [CharZero 𝕜] in
theorem ftEvalG_add (P Q : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftAdd P Q) z = ftEvalG cf sf p P z + ftEvalG cf sf p Q z :=
  ftEvalG_append cf sf p P Q z

omit [CharZero 𝕜] in
theorem ftEvalG_neg (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftNeg P) z = -ftEvalG cf sf p P z := by
  induction P with
  | nil => simp [ftNeg]
  | cons m P ih =>
    simp only [ftNeg, List.map_cons, ftEvalG_cons] at ih ⊢
    rw [ih]; simp only [ftMonoEvalG]; push_cast; ring

omit [CharZero 𝕜] in
theorem ftEvalG_sub (P Q : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftSub P Q) z = ftEvalG cf sf p P z - ftEvalG cf sf p Q z := by
  simp [ftSub, ftEvalG_add, ftEvalG_neg, sub_eq_add_neg]

theorem ftEvalG_smul (r : ℚ) (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftSmul r P) z = (r : 𝕜) * ftEvalG cf sf p P z := by
  induction P with
  | nil => simp [ftSmul]
  | cons m P ih =>
    simp only [ftSmul, List.map_cons, ftEvalG_cons] at ih ⊢
    rw [ih]; simp only [ftMonoEvalG]; push_cast; ring

omit [CharZero 𝕜] in
theorem ftJProd_nil (J : Fin n → 𝕜) : ftJProd [] J = 1 := by simp [ftJProd]

omit [CharZero 𝕜] in
theorem ftPhase_nil (φ : Fin n → 𝕜) : ftPhase [] φ = 0 := by simp [ftPhase]

omit [CharZero 𝕜] in
theorem ftEvalG_const (h : FTTrig cf sf) (r : ℚ) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftConst r) z = (r : 𝕜) := by
  simp [ftConst, ftMonoEvalG, ftJProd_nil, ftPhase_nil, h.cos_zero, h.sin_zero]

omit [CharZero 𝕜] in
theorem ftJProd_unit (j e : ℕ) (hj : j < n) (J : Fin n → 𝕜) :
    ftJProd (unitExp j e) J = J ⟨j, hj⟩ ^ e := by
  unfold ftJProd
  rw [Finset.prod_eq_single ⟨j, hj⟩]
  · simp only [getD_unitExp]; simp
  · intro k _ hk
    have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
    simp only [getD_unitExp, this, ite_false]; simp
  · simp

omit [CharZero 𝕜] in
theorem ftEvalG_jVar (h : FTTrig cf sf) (i : Fin n) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftJVar i) z = z.2 i := by
  simp [ftJVar, ftMonoEvalG, ftJProd_unit _ _ i.2, ftPhase_nil, h.cos_zero, h.sin_zero]

omit [CharZero 𝕜] in
theorem ftEvalG_cosMode (k : List ℤ) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftCosMode k) z = cf (2 * p * ftPhase k z.1) := by
  simp [ftCosMode, ftMonoEvalG, ftJProd_nil]

omit [CharZero 𝕜] in
theorem ftEvalG_sinMode (k : List ℤ) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftSinMode k) z = sf (2 * p * ftPhase k z.1) := by
  simp [ftSinMode, ftMonoEvalG, ftJProd_nil]

/-! ### Products -/

omit [CharZero 𝕜] in
theorem ftPhase_congr {k k' : List ℤ} (hk : ∀ i, k.getD i 0 = k'.getD i 0) (φ : Fin n → 𝕜) :
    ftPhase k φ = ftPhase k' φ := by
  unfold ftPhase; exact Finset.sum_congr rfl fun i _ => by rw [hk]

omit [CharZero 𝕜] in
theorem ftJProd_congr {a a' : List ℕ} (ha : ∀ i, a.getD i 0 = a'.getD i 0) (J : Fin n → 𝕜) :
    ftJProd a J = ftJProd a' J := by
  unfold ftJProd; exact Finset.prod_congr rfl fun i _ => by rw [ha]

omit [CharZero 𝕜] in
theorem ftPhase_add (k k' : List ℤ) (φ : Fin n → 𝕜) :
    ftPhase (ftAddPadZ k k') φ = ftPhase k φ + ftPhase k' φ := by
  unfold ftPhase
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [ftGetD_addPadZ]; push_cast; ring

omit [CharZero 𝕜] in
theorem ftPhase_neg (k : List ℤ) (φ : Fin n → 𝕜) :
    ftPhase (k.map Neg.neg) φ = -ftPhase k φ := by
  unfold ftPhase
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [ftGetD_neg]; push_cast; ring

omit [CharZero 𝕜] in
theorem ftJProd_add (a a' : List ℕ) (J : Fin n → 𝕜) :
    ftJProd (addPad a a') J = ftJProd a J * ftJProd a' J := by
  unfold ftJProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [getD_addPad, pow_add]

/-- Product of two monomials by the product-to-sum formulas (two monomials: `k + k'`, `k - k'`). -/
def ftMonoMul (m m' : FTMono) : FTPoly :=
  [⟨ftAddPadZ m.k m'.k, addPad m.α m'.α, m.e + m'.e, (m.c * m'.c - m.s * m'.s) / 2,
      (m.c * m'.s + m.s * m'.c) / 2⟩,
   ⟨ftAddPadZ m.k (m'.k.map Neg.neg), addPad m.α m'.α, m.e + m'.e,
      (m.c * m'.c + m.s * m'.s) / 2, (m.s * m'.c - m.c * m'.s) / 2⟩]

/-- Product (pairwise products of monomials). -/
def ftMul (P Q : FTPoly) : FTPoly := P.flatMap fun m => Q.flatMap (ftMonoMul m)

theorem ftMonoEvalG_mul (h : FTTrig cf sf) (m m' : FTMono) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftMonoMul m m') z = ftMonoEvalG cf sf p m z * ftMonoEvalG cf sf p m' z := by
  have h2 : (2 : 𝕜) ≠ 0 := two_ne_zero
  simp only [ftMonoMul, ftEvalG_cons, ftEvalG_nil, add_zero, ftMonoEvalG, ftPhase_add,
    ftPhase_neg, ftJProd_add, pow_add]
  have e1 : 2 * p * (ftPhase m.k z.1 + ftPhase m'.k z.1) =
      2 * p * ftPhase m.k z.1 + 2 * p * ftPhase m'.k z.1 := by ring
  have e2 : 2 * p * (ftPhase m.k z.1 + -ftPhase m'.k z.1) =
      2 * p * ftPhase m.k z.1 + -(2 * p * ftPhase m'.k z.1) := by ring
  rw [e1, e2, h.cos_add, h.sin_add, h.cos_add, h.sin_add, h.cos_neg, h.sin_neg]
  push_cast
  ring

theorem ftEvalG_mulMono (h : FTTrig cf sf) (m : FTMono) (Q : FTPoly)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (Q.flatMap (ftMonoMul m)) z =
      ftMonoEvalG cf sf p m z * ftEvalG cf sf p Q z := by
  induction Q with
  | nil => simp
  | cons m' Q ih =>
    rw [List.flatMap_cons, ftEvalG_append, ftMonoEvalG_mul cf sf p h, ih, ftEvalG_cons]; ring

theorem ftEvalG_mul (h : FTTrig cf sf) (P Q : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftMul P Q) z = ftEvalG cf sf p P z * ftEvalG cf sf p Q z := by
  induction P with
  | nil => simp [ftMul]
  | cons m P ih =>
    have : ftMul (m :: P) Q = Q.flatMap (ftMonoMul m) ++ ftMul P Q := by simp [ftMul]
    rw [this, ftEvalG_append, ftEvalG_mulMono cf sf p h, ih, ftEvalG_cons]; ring

/-! ### Normalization and the identity checker -/

/-- Trim trailing zeros of both lists, fix the sign of `k` (first nonzero entry positive, flipping
`s`), and clear `s` when `k = 0`. -/
def ftMonoCanon (m : FTMono) : FTMono :=
  if ftFirstNeg (ftTrimZ m.k) then
    ⟨(ftTrimZ m.k).map Neg.neg, trimExp m.α, m.e, m.c, -m.s⟩
  else if ftTrimZ m.k = [] then ⟨[], trimExp m.α, m.e, m.c, 0⟩
  else ⟨ftTrimZ m.k, trimExp m.α, m.e, m.c, m.s⟩

omit [CharZero 𝕜] in
theorem ftJProd_trim (a : List ℕ) (J : Fin n → 𝕜) : ftJProd (trimExp a) J = ftJProd a J :=
  ftJProd_congr (getD_trimExp a) J

omit [CharZero 𝕜] in
theorem ftMonoEvalG_canon (h : FTTrig cf sf) (m : FTMono) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftMonoEvalG cf sf p (ftMonoCanon m) z = ftMonoEvalG cf sf p m z := by
  have hp : ftPhase (ftTrimZ m.k) z.1 = ftPhase m.k z.1 := ftPhase_congr (ftGetD_trimZ _) _
  unfold ftMonoCanon
  split_ifs with h1 h2
  · simp only [ftMonoEvalG, ftPhase_neg, hp, ftJProd_trim]
    have : 2 * p * -ftPhase m.k z.1 = -(2 * p * ftPhase m.k z.1) := by ring
    rw [this, h.cos_neg, h.sin_neg]; push_cast; ring
  · simp only [ftMonoEvalG, ftJProd_trim]
    have : ftPhase m.k z.1 = 0 := by rw [← hp, h2, ftPhase_nil]
    simp only [ftPhase_nil, this, mul_zero, h.sin_zero]
  · simp only [ftMonoEvalG, hp, ftJProd_trim]

/-- Insert a monomial, merging with an existing one with the same `(k, α, e)` key. -/
def ftInsertMono (m : FTMono) : FTPoly → FTPoly
  | [] => [m]
  | m' :: P =>
    if m'.k = m.k ∧ m'.α = m.α ∧ m'.e = m.e then
      ⟨m'.k, m'.α, m'.e, m'.c + m.c, m'.s + m.s⟩ :: P
    else m' :: ftInsertMono m P

theorem ftEvalG_insertMono (m : FTMono) (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftInsertMono m P) z = ftMonoEvalG cf sf p m z + ftEvalG cf sf p P z := by
  induction P with
  | nil => simp [ftInsertMono]
  | cons m' P ih =>
    unfold ftInsertMono
    split_ifs with hh
    · obtain ⟨h1, h2, h3⟩ := hh
      simp only [ftEvalG_cons, ftMonoEvalG, ← h1, ← h2, ← h3]
      push_cast; ring
    · rw [ftEvalG_cons, ih, ftEvalG_cons]; ring

/-- Merge a list of monomials by key. -/
def ftMerge (P : FTPoly) : FTPoly := P.foldr ftInsertMono []

theorem ftEvalG_merge (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftMerge P) z = ftEvalG cf sf p P z := by
  induction P with
  | nil => simp [ftMerge]
  | cons m P ih =>
    have : ftMerge (m :: P) = ftInsertMono m (ftMerge P) := rfl
    rw [this, ftEvalG_insertMono, ih, ftEvalG_cons]

omit [CharZero 𝕜] in
theorem ftEvalG_canonmap (h : FTTrig cf sf) (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (P.map ftMonoCanon) z = ftEvalG cf sf p P z := by
  induction P with
  | nil => simp
  | cons m P ih => simp only [List.map_cons, ftEvalG_cons, ftMonoEvalG_canon cf sf p h, ih]

omit [CharZero 𝕜] in
theorem ftEvalG_filter (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (P.filter fun m => decide (m.c ≠ 0 ∨ m.s ≠ 0)) z = ftEvalG cf sf p P z := by
  induction P with
  | nil => simp
  | cons m P ih =>
    by_cases hm : m.c ≠ 0 ∨ m.s ≠ 0
    · rw [List.filter_cons_of_pos (by simpa using hm), ftEvalG_cons, ftEvalG_cons, ih]
    · have hc : m.c = 0 := by by_contra hc; exact hm (Or.inl hc)
      have hs : m.s = 0 := by by_contra hs; exact hm (Or.inr hs)
      rw [List.filter_cons_of_neg (by simpa using hm), ih, ftEvalG_cons]
      simp [ftMonoEvalG, hc, hs]

/-- Normal form: canonical monomials, merged by key, zero terms dropped. -/
def ftNormalize (P : FTPoly) : FTPoly :=
  (ftMerge (P.map ftMonoCanon)).filter fun m => decide (m.c ≠ 0 ∨ m.s ≠ 0)

theorem ftEvalG_normalize (h : FTTrig cf sf) (P : FTPoly) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    ftEvalG cf sf p (ftNormalize P) z = ftEvalG cf sf p P z := by
  rw [ftNormalize, ftEvalG_filter, ftEvalG_merge, ftEvalG_canonmap cf sf p h]

/-- The identity checker: `ftNormalize (P - Q) = []`. -/
def ftEqCheck (P Q : FTPoly) : Bool := (ftNormalize (ftSub P Q)).isEmpty

theorem ftEvalG_eq_of_eqCheck (h : FTTrig cf sf) {P Q : FTPoly} (hc : ftEqCheck P Q = true)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) : ftEvalG cf sf p P z = ftEvalG cf sf p Q z := by
  have h0 : ftNormalize (ftSub P Q) = [] := by simpa [ftEqCheck] using hc
  have := ftEvalG_normalize cf sf p h (ftSub P Q) z
  rw [h0, ftEvalG_sub] at this
  exact sub_eq_zero.1 this.symm

end Generic

/-! ### Real and complex evaluation -/

variable {n : ℕ}

/-- Real evaluation at a point `(φ, J)`. -/
def ftEvalR (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ftEvalG Real.cos Real.sin Real.pi P x

/-- Complex evaluation at a point `(φ, J)`. -/
def ftEvalC (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  ftEvalG Complex.cos Complex.sin (Real.pi : ℂ) P z

theorem ftEvalC_ofReal (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalC P ((fun i => ((x.1 i : ℝ) : ℂ), fun i => ((x.2 i : ℝ) : ℂ)) :
      (Fin n → ℂ) × (Fin n → ℂ)) = ((ftEvalR P x : ℝ) : ℂ) := by
  induction P with
  | nil => simp [ftEvalC, ftEvalR]
  | cons m P ih =>
    simp only [ftEvalC, ftEvalR, ftEvalG_cons] at ih ⊢
    rw [ih]
    push_cast
    simp [ftMonoEvalG, ftPhase, ftJProd, Complex.ofReal_cos, Complex.ofReal_sin]

theorem ftEvalR_add (P Q : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftAdd P Q) x = ftEvalR P x + ftEvalR Q x := ftEvalG_add _ _ _ P Q x

theorem ftEvalC_add (P Q : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftAdd P Q) z = ftEvalC P z + ftEvalC Q z := ftEvalG_add _ _ _ P Q z

theorem ftEvalR_neg (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftNeg P) x = -ftEvalR P x := ftEvalG_neg _ _ _ P x

theorem ftEvalC_neg (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftNeg P) z = -ftEvalC P z := ftEvalG_neg _ _ _ P z

theorem ftEvalR_sub (P Q : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftSub P Q) x = ftEvalR P x - ftEvalR Q x := ftEvalG_sub _ _ _ P Q x

theorem ftEvalC_sub (P Q : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftSub P Q) z = ftEvalC P z - ftEvalC Q z := ftEvalG_sub _ _ _ P Q z

theorem ftEvalR_smul (r : ℚ) (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftSmul r P) x = (r : ℝ) * ftEvalR P x := ftEvalG_smul _ _ _ r P x

theorem ftEvalC_smul (r : ℚ) (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftSmul r P) z = (r : ℂ) * ftEvalC P z := ftEvalG_smul _ _ _ r P z

theorem ftEvalR_mul (P Q : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftMul P Q) x = ftEvalR P x * ftEvalR Q x := ftEvalG_mul _ _ _ ftTrig_real P Q x

theorem ftEvalC_mul (P Q : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftMul P Q) z = ftEvalC P z * ftEvalC Q z := ftEvalG_mul _ _ _ ftTrig_complex P Q z

theorem ftEvalR_const (r : ℚ) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ftEvalR (ftConst r) x = r :=
  ftEvalG_const _ _ _ ftTrig_real r x

theorem ftEvalC_const (r : ℚ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ftEvalC (ftConst r) z = r :=
  ftEvalG_const _ _ _ ftTrig_complex r z

theorem ftEvalR_jVar (i : Fin n) (x : (Fin n → ℝ) × (Fin n → ℝ)) : ftEvalR (ftJVar i) x = x.2 i :=
  ftEvalG_jVar _ _ _ ftTrig_real i x

theorem ftEvalC_jVar (i : Fin n) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ftEvalC (ftJVar i) z = z.2 i :=
  ftEvalG_jVar _ _ _ ftTrig_complex i z

theorem ftEvalR_normalize (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalR (ftNormalize P) x = ftEvalR P x := ftEvalG_normalize _ _ _ ftTrig_real P x

theorem ftEvalC_normalize (P : FTPoly) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ftEvalC (ftNormalize P) z = ftEvalC P z := ftEvalG_normalize _ _ _ ftTrig_complex P z

/-- Soundness of the identity checker over `ℝ`. -/
theorem ftEvalR_eq_of_eqCheck {P Q : FTPoly} (h : ftEqCheck P Q = true)
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : ftEvalR P x = ftEvalR Q x :=
  ftEvalG_eq_of_eqCheck _ _ _ ftTrig_real h x

/-- Soundness of the identity checker over `ℂ`. -/
theorem ftEvalC_eq_of_eqCheck {P Q : FTPoly} (h : ftEqCheck P Q = true)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) : ftEvalC P z = ftEvalC Q z :=
  ftEvalG_eq_of_eqCheck _ _ _ ftTrig_complex h z

/-! ### Typing data -/

/-- `FTFits n P`: all frequency and exponent entries at indices `≥ n` vanish. -/
def FTFits (n : ℕ) (P : FTPoly) : Prop :=
  ∀ m ∈ P, ∀ k, n ≤ k → m.k.getD k 0 = 0 ∧ m.α.getD k 0 = 0

/-- The Boolean checker for `FTFits`. -/
def ftFitsCheck (n : ℕ) (P : FTPoly) : Bool :=
  P.all fun m => decide (m.k.length ≤ n) && decide (m.α.length ≤ n)

theorem ftFits_of_check {n : ℕ} {P : FTPoly} (h : ftFitsCheck n P = true) : FTFits n P := by
  intro m hm k hk
  have := List.all_eq_true.1 h m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨ftGetD_zero_of_length_le m.k k (by omega), ftGetD_zero_of_length_le m.α k (by omega)⟩

theorem ftFits_nil (n : ℕ) : FTFits n ([] : FTPoly) := by simp [FTFits]

theorem ftFits_add {P Q : FTPoly} (hP : FTFits n P) (hQ : FTFits n Q) : FTFits n (ftAdd P Q) := by
  intro m hm k hk
  rcases List.mem_append.1 hm with h | h
  exacts [hP m h k hk, hQ m h k hk]

theorem ftFits_neg {P : FTPoly} (hP : FTFits n P) : FTFits n (ftNeg P) := by
  intro m hm k hk
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  exact hP m' hm' k hk

theorem ftFits_sub {P Q : FTPoly} (hP : FTFits n P) (hQ : FTFits n Q) : FTFits n (ftSub P Q) :=
  ftFits_add hP (ftFits_neg hQ)

theorem ftFits_smul (r : ℚ) {P : FTPoly} (hP : FTFits n P) : FTFits n (ftSmul r P) := by
  intro m hm k hk
  obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
  exact hP m' hm' k hk

theorem ftFits_mul {P Q : FTPoly} (hP : FTFits n P) (hQ : FTFits n Q) : FTFits n (ftMul P Q) := by
  intro m hm k hk
  obtain ⟨m1, hm1, hm⟩ := List.mem_flatMap.1 hm
  obtain ⟨m2, hm2, hm⟩ := List.mem_flatMap.1 hm
  have h1 := hP m1 hm1 k hk
  have h2 := hQ m2 hm2 k hk
  simp only [ftMonoMul, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;>
    simp only [ftGetD_addPadZ, getD_addPad, ftGetD_neg, h1.1, h1.2, h2.1, h2.2] <;> simp

theorem ftFits_const (r : ℚ) : FTFits n (ftConst r) := by
  intro m hm k _
  obtain rfl : m = ⟨[], [], 0, r, 0⟩ := List.mem_singleton.1 hm
  exact ⟨List.getD_nil, List.getD_nil⟩

theorem ftFits_jVar {j : ℕ} (hj : j < n) : FTFits n (ftJVar j) := by
  intro m hm k hk
  obtain rfl : m = ⟨[], unitExp j 1, 0, 1, 0⟩ := List.mem_singleton.1 hm
  have : k ≠ j := by omega
  exact ⟨List.getD_nil, by simp only [getD_unitExp, this, ite_false]⟩

theorem ftFits_cosMode {k : List ℤ} (hk : k.length ≤ n) : FTFits n (ftCosMode k) := by
  intro m hm i hi
  obtain rfl : m = ⟨k, [], 0, 1, 0⟩ := List.mem_singleton.1 hm
  exact ⟨ftGetD_zero_of_length_le k i (by omega), List.getD_nil⟩

theorem ftFits_sinMode {k : List ℤ} (hk : k.length ≤ n) : FTFits n (ftSinMode k) := by
  intro m hm i hi
  obtain rfl : m = ⟨k, [], 0, 0, 1⟩ := List.mem_singleton.1 hm
  exact ⟨ftGetD_zero_of_length_le k i (by omega), List.getD_nil⟩

end KAM.EffectiveStability
