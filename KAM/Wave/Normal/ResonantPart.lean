/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.ResonantBalance

/-!
# The resonant quartic part `Ḡ` in complex coordinates (blueprint `bpW:w0n:AB`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

Finite-mode version of blueprint Definition `bpW:w0n:Qdef`, Step `stepW:w0n:resavg` and Theorem
`bpW:w0n:AB`. In the complex coordinates `z = (q + i p)/√2` of `bpW:w0:z` the quartic functional
`G` is `(1/16) ∑ g̃_{ijkl} ∏ (z_{i_s} + z̄_{i_s})` (`KAM.Wave.quarticG_eq_complex`), a sum over
index tuples and sign patterns `e ∈ Bool⁴` of the monomials `quarticMonomial`. A monomial is
*resonant* when its divisor `∑ ± λ_{i_s}` vanishes. `KAM.Wave.resonantQuarticPart S z` is the sum
of the resonant monomials over the index tuples satisfying `S`; with `S` the tuples containing a
tangential mode (`J = {1, 2}`, the first two modes) this is `Ḡ`, the resonant part of `G^tan`.

* `resonantQuarticPart_polar`: on `z_j = r_j e^{-iφ_j}` the resonant part is independent of the
  angles and equals a real polynomial in the actions (uses `quartic_nonresonance` through
  `signBalanced_of_resonant`: a resonant monomial with `g ≠ 0` is a product of `I_a = r_a²`).
* `resonantQuarticReal_all`: the full resonant part equals the angle average `⟨G⟩` of
  `KAM/Wave/Normal/ActionCoeff.lean` (`3/(16π)(4(∑ I_j/λ_j)² - ∑ I_j²/λ_j²)`).
* `resonantQuarticPart_tangential_eq` (**`bpW:w0n:AB`**, finite modes `N = 2 + n`): for actions
  `I ∈ ℝ₊²`, `Z ∈ ℝ₊ⁿ` and every angle vector `φ`, `Ḡ(z) = ½⟨AI, I⟩ + ⟨BI, Z⟩` with the
  corrected coefficients of `actionA`, `actionB`.

Not covered (remaining for the full source node): the extension from finitely many modes to the
weighted sequence space (blueprint "extended by the absolutely convergent formula"), and the
statement for arbitrary complex `w_j w_{-j}` (not only `|z_j|² = I_j ≥ 0` with free phases).
-/

@[expose] public noncomputable section

open Classical Real

namespace KAM.Wave

/-- `true ↦ w`, `false ↦ w̄`. -/
def conjSelect (b : Bool) (w : ℂ) : ℂ := if b then w else (starRingEnd ℂ) w

def quarticMonomial {N : ℕ} (z : Fin N → ℂ) (e : Bool × Bool × Bool × Bool) (i j k l : Fin N) : ℂ :=
  conjSelect e.1 (z i) * conjSelect e.2.1 (z j) * conjSelect e.2.2.1 (z k) *
      conjSelect e.2.2.2 (z l)

def quarticDivisor {N : ℕ} (m : ℝ) (hm : 0 <
    m) (e : Bool × Bool × Bool × Bool) (i j k l : Fin N) : ℝ :=
  (boolSign e.1 : ℝ) * lamMode m hm i + (boolSign e.2.1 : ℝ) * lamMode m hm j
    + (boolSign e.2.2.1 : ℝ) * lamMode m hm k + (boolSign e.2.2.2 : ℝ) * lamMode m hm l

def normQuarticCoeff {N : ℕ} (m : ℝ) (hm : 0 < m) (i j k l : Fin N) : ℝ :=
  gN i j k l / (Real.sqrt (lamMode m hm i) * Real.sqrt (lamMode m hm j)
    * Real.sqrt (lamMode m hm k) * Real.sqrt (lamMode m hm l))

theorem conjSelect_polar (b : Bool) (r φ : ℝ) :
    conjSelect b ((r : ℂ) * Complex.exp (-(Complex.I * φ))) =
      (r : ℂ) * Complex.exp (-(Complex.I * ((boolSign b : ℝ) * φ : ℝ))) := by
  cases b
  · simp [conjSelect, boolSign, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  · simp [conjSelect, boolSign]

theorem quarticMonomial_polar {N : ℕ} (r φ : Fin N → ℝ) (e : Bool × Bool × Bool × Bool)
    (i j k l : Fin N) (h : signBalanced e i j k l) :
    quarticMonomial (fun t => (r t : ℂ) * Complex.exp (-(Complex.I * φ t))) e i j k l
      = ((r i * r j * r k * r l : ℝ) : ℂ) := by
  have hs := signBalanced_sum_zero e i j k l h φ
  unfold quarticMonomial
  simp only [conjSelect_polar]
  have : (r i : ℂ) * Complex.exp (-(Complex.I * ((boolSign e.1 : ℝ) * φ i : ℝ)))
      * ((r j : ℂ) * Complex.exp (-(Complex.I * ((boolSign e.2.1 : ℝ) * φ j : ℝ))))
      * ((r k : ℂ) * Complex.exp (-(Complex.I * ((boolSign e.2.2.1 : ℝ) * φ k : ℝ))))
      * ((r l : ℂ) * Complex.exp (-(Complex.I * ((boolSign e.2.2.2 : ℝ) * φ l : ℝ))))
      = ((r i * r j * r k * r l : ℝ) : ℂ) * Complex.exp (-(Complex.I * (((boolSign e.1 : ℝ) * φ i
        + (boolSign e.2.1 : ℝ) * φ j + (boolSign e.2.2.1 : ℝ) * φ k + (boolSign e.2.2.2 : ℝ) *
            φ l : ℝ) : ℂ))) := by
    push_cast
    simp only [mul_add, neg_add, Complex.exp_add]
    ring
  rw [this, hs]
  simp

theorem resonantQuartic_term_eq {N : ℕ} (m : ℝ) (hm : 0 < m) (r φ : Fin N → ℝ)
    (e : Bool × Bool × Bool × Bool) (i j k l : Fin N) :
    (normQuarticCoeff m hm i j k l : ℂ) * (if quarticDivisor m hm e i j k l = 0 then
        quarticMonomial (fun t => (r t : ℂ) * Complex.exp (-(Complex.I * φ t))) e i j k l else 0)
      = (normQuarticCoeff m hm i j k l : ℂ) * (if signBalanced e i j k l then ((r i * r j * r k *
          r l : ℝ) : ℂ)
        else 0) := by
  by_cases hg : gN i j k l = 0
  · have : normQuarticCoeff m hm i j k l = 0 := by simp [normQuarticCoeff, hg]
    simp [this]
  · by_cases hb : signBalanced e i j k l
    · have hd : quarticDivisor m hm e i j k l =
        0 := signBalanced_sum_zero e i j k l hb (lamMode m hm)
      simp only [hd, hb, ↓reduceIte]
      rw [quarticMonomial_polar r φ e i j k l hb]
    · have hd : ¬ quarticDivisor m hm e i j k l =
        0 := fun hd => hb (signBalanced_of_resonant m hm e i j k l hg hd)
      simp [hd, hb]

/-- The resonant part of the complex quartic expansion of `G`, restricted to the index tuples
satisfying `S`: the sum of the monomials `g̃ ∏ (z or z̄)` with vanishing divisor. -/
def resonantQuarticPart {N : ℕ} (S : Fin N → Fin N → Fin N → Fin N → Prop) (m : ℝ) (hm : 0 < m)
    (z : Fin N → ℂ) : ℂ :=
  (1 / 16) * ∑ i, ∑ j, ∑ k, ∑ l, if S i j k l then (normQuarticCoeff m hm i j k l : ℂ) *
    ∑ e : Bool × Bool × Bool × Bool,
      (if quarticDivisor m hm e i j k l = 0 then quarticMonomial z e i j k l else 0) else 0

/-- Real-coefficient form of the resonant sum. -/
def resonantQuarticReal {N : ℕ} (S : Fin N → Fin N → Fin N → Fin N → Prop) (m : ℝ) (hm : 0 < m)
    (r : Fin N → ℝ) : ℝ :=
  (1 / 16) * ∑ i, ∑ j, ∑ k, ∑ l, if S i j k l then normQuarticCoeff m hm i j k l * (r i * r j *
      r k * r l)
    * (4 * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
      + (if i = l ∧ j = k then 1 else 0)) - 6 * (if i = j ∧ j = k ∧ k = l then 1 else 0)) else 0

theorem resonantQuartic_term_sum_eq {N : ℕ} (m : ℝ) (hm : 0 < m) (r φ : Fin N →
    ℝ) (i j k l : Fin N) :
    (normQuarticCoeff m hm i j k l : ℂ) * ∑ e : Bool × Bool × Bool × Bool,
      (if quarticDivisor m hm e i j k l = 0 then
        quarticMonomial (fun t => (r t : ℂ) * Complex.exp (-(Complex.I * φ t))) e i j k l else 0)
      = ((normQuarticCoeff m hm i j k l * (r i * r j * r k * r l)
        * (4 * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
          + (if i = l ∧ j = k then 1 else 0)) - 6 * (if i = j ∧ j = k ∧ k = l then 1 else 0))
          : ℝ) : ℂ) := by
  rw [Finset.mul_sum]
  simp only [resonantQuartic_term_eq]
  rw [← Finset.mul_sum, ← signBalanced_count]
  have : ∀ e : Bool × Bool × Bool × Bool, (if signBalanced e i j k l then ((r i * r j * r k *
      r l : ℝ) : ℂ)
      else 0) = ((r i * r j * r k * r l : ℝ) : ℂ) *
          (((if signBalanced e i j k l then (1 : ℝ) else 0) : ℝ)
      : ℂ) := fun e => by split_ifs <;> simp
  simp only [this, ← Finset.mul_sum]
  push_cast
  ring

theorem resonantQuarticPart_polar {N : ℕ} (S : Fin N → Fin N → Fin N → Fin N → Prop) (m : ℝ)
    (hm : 0 < m) (r φ : Fin N → ℝ) :
    resonantQuarticPart S m hm (fun t => (r t : ℂ) * Complex.exp (-(Complex.I * φ t)))
      = (resonantQuarticReal S m hm r : ℂ) := by
  unfold resonantQuarticPart resonantQuarticReal
  have key : ∀ i j k l : Fin N, (if S i j k l then (normQuarticCoeff m hm i j k l : ℂ) *
      ∑ e : Bool × Bool × Bool × Bool,
        (if quarticDivisor m hm e i j k l = 0 then
          quarticMonomial (fun t => (r t : ℂ) * Complex.exp (-(Complex.I * φ t))) e i j k l else 0)
      else 0) = (((if S i j k l then normQuarticCoeff m hm i j k l * (r i * r j * r k * r l)
        * (4 * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
          + (if i = l ∧ j = k then 1 else 0)) - 6 * (if i = j ∧ j = k ∧ k = l then 1 else 0))
        else 0 : ℝ)) : ℂ) := by
    intro i j k l
    by_cases hS : S i j k l
    · simp only [hS, ↓reduceIte]
      exact resonantQuartic_term_sum_eq m hm r φ i j k l
    · simp [hS]
  simp only [key]
  push_cast
  rfl

/-- All index tuples. -/
def allQuarticTuples {N : ℕ} (_ _ _ _ : Fin N) : Prop := True

/-- The tangential modes `J = {1, 2}` are the first two. -/
def isTangentialMode {N : ℕ} (j : Fin N) : Prop := j.val < 2

/-- Index tuples containing at least one tangential mode (the monomials of `G^tan`). -/
def tangentialQuarticTuple {N : ℕ} (i j k l : Fin N) : Prop := isTangentialMode i ∨
    isTangentialMode j ∨ isTangentialMode k ∨ isTangentialMode l

/-- Index tuples with all modes normal (the monomials of `G^nor`). -/
def normalQuarticTuple {N : ℕ} (i j k l : Fin N) : Prop := ¬ isTangentialMode i ∧
    ¬ isTangentialMode j ∧ ¬ isTangentialMode k ∧ ¬ isTangentialMode l

theorem resonantQuarticReal_split {N : ℕ} (m : ℝ) (hm : 0 < m) (r : Fin N → ℝ) :
    resonantQuarticReal tangentialQuarticTuple m hm r =
        resonantQuarticReal allQuarticTuples m hm r -
        resonantQuarticReal normalQuarticTuple m hm r := by
  unfold resonantQuarticReal
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : tangentialQuarticTuple i j k l ↔ ¬ normalQuarticTuple i j k l := by
    unfold tangentialQuarticTuple normalQuarticTuple; tauto
  by_cases h : normalQuarticTuple i j k l
  · have h' : ¬ tangentialQuarticTuple i j k l := fun ht => (this.1 ht) h
    simp [h, h', allQuarticTuples]
  · have h' : tangentialQuarticTuple i j k l := this.2 h
    simp [h, h', allQuarticTuples]


theorem resonantQuarticReal_all {N : ℕ} (m : ℝ) (hm : 0 < m) (r : Fin N → ℝ) :
    resonantQuarticReal allQuarticTuples m hm r = 3 / (16 * π) *
      (4 * (∑ j, r j ^ 2 / lamMode m hm j) ^ 2 - ∑ j, (r j ^ 2 / lamMode m hm j) ^ 2) := by
  set a : Fin N → ℝ := fun j => Real.sqrt 2 * r j / Real.sqrt (lamMode m hm j) with ha
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hl : ∀ j : Fin N,
      Real.sqrt (lamMode m hm j) ≠ 0 := fun j => (Real.sqrt_pos.2 (lamMode_pos m hm j)).ne'
  have hpt : ∀ i j k l : Fin N, (if allQuarticTuples i j k l then normQuarticCoeff m hm i j k l *
      (r i * r j * r k * r l)
      * (4 * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
        + (if i = l ∧ j = k then 1 else 0)) - 6 * (if i = j ∧ j = k ∧ k = l then 1 else 0))
      else 0) = 4 * ((gN i j k l * (a i * a j * a k * a l)) *
        ((1 / 4) * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
          + (if i = l ∧ j = k then 1 else 0)) - (3 / 8) * (if i = j ∧ j = k ∧ k =
              l then 1 else 0))) := by
    intro i j k l
    have e4 : Real.sqrt 2 ^ 4 = 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]; norm_num
    have := hl i
    have := hl j
    have := hl k
    have := hl l
    have hT : allQuarticTuples i j k l := trivial
    simp only [hT, ↓reduceIte, normQuarticCoeff, ha]
    field_simp
    rw [e4]
    ring
  unfold resonantQuarticReal
  simp only [hpt, ← Finset.mul_sum]
  rw [sum_quartic_moment]
  have hsq : ∀ j, a j ^ 2 = 2 * (r j ^ 2 / lamMode m hm j) := by
    intro j
    simp only [ha]
    rw [div_pow, mul_pow, hs, Real.sq_sqrt (lamMode_pos m hm j).le]
    ring
  have h2 : ∑ t, a t ^ 2 = 2 * ∑ j, r j ^ 2 / lamMode m hm j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => hsq j
  have h4 : ∑ t, a t ^ 4 = 4 * ∑ j, (r j ^ 2 / lamMode m hm j) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a j ^ 4 = (a j ^ 2) ^ 2 by ring, hsq]; ring
  rw [h2, h4]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring


theorem resonantQuarticReal_normal {N : ℕ} (m : ℝ) (hm : 0 < m) (r : Fin N → ℝ) :
    resonantQuarticReal normalQuarticTuple m hm r
      = resonantQuarticReal allQuarticTuples m hm
        (fun j => if isTangentialMode j then 0 else r j) := by
  unfold resonantQuarticReal
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hT : allQuarticTuples i j k l := trivial
  by_cases h : normalQuarticTuple i j k l
  · obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [normalQuarticTuple, h1, h2, h3, h4, not_false_eq_true, and_self, hT, ↓reduceIte]
  · have : tangentialQuarticTuple i j k l := by
      unfold tangentialQuarticTuple normalQuarticTuple at *; tauto
    have hz : (if isTangentialMode i then 0 else r i) * (if isTangentialMode j then 0 else r j)
        * (if isTangentialMode k then 0 else r k) * (if isTangentialMode l then 0 else r l) =
            0 := by
      unfold tangentialQuarticTuple at this
      rcases this with h | h | h | h <;> simp [h]
    simp only [h, hT, ↓reduceIte, hz]
    simp

theorem resonantQuarticPart_tangential_eq {n : ℕ} (m : ℝ) (hm : 0 < m) (I : Fin 2 → ℝ) (Z : Fin n →
    ℝ)
    (hI : ∀ i, 0 ≤ I i) (hZ : ∀ j, 0 ≤ Z j) (φ : Fin (2 + n) → ℝ) :
    resonantQuarticPart tangentialQuarticTuple m hm
        (fun t => (Real.sqrt (Fin.append I Z t) : ℂ) * Complex.exp (-(Complex.I * φ t)))
      = ((1 / 2 * ∑ i, ∑ i', actionA m hm i i' * I i * I i'
        + ∑ j, ∑ i, actionB m hm j i * I i * Z j : ℝ) : ℂ) := by
  have hnn : ∀ I' : Fin 2 → ℝ, (∀ i, 0 ≤ I' i) → ∀ j, 0 ≤ (Fin.append I' Z) j := by
    intro I' hI' j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simpa using hI' i
    · simpa using hZ j
  rw [resonantQuarticPart_polar, resonantQuarticReal_split, resonantQuarticReal_normal,
      resonantQuarticReal_all,
    resonantQuarticReal_all]
  have hr2 : ∀ j : Fin (2 + n),
      (if isTangentialMode j then (0 : ℝ) else Real.sqrt (Fin.append I Z j)) ^ 2
        = Fin.append (0 : Fin 2 → ℝ) Z j := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · have : isTangentialMode (Fin.castAdd n i) := by
        have := i.isLt
        simp only [isTangentialMode, Fin.val_castAdd]; omega
      simp [this]
    · have : ¬ isTangentialMode (Fin.natAdd 2 j) := by
        simp only [isTangentialMode, Fin.val_natAdd]; omega
      simp only [this, ite_false, Fin.append_right]
      exact Real.sq_sqrt (hZ j)
  have e1 := avgG_eq m hm (Fin.append I Z) (hnn I hI)
  have e2 := avgG_eq m hm (Fin.append (0 : Fin 2 → ℝ) Z) (hnn 0 (fun _ => le_rfl))
  have sq1 : ∀ j, Real.sqrt (Fin.append I Z j) ^ 2 = Fin.append I Z j :=
    fun j => Real.sq_sqrt (hnn I hI j)
  simp only [sq1, hr2]
  have := partial_avgG_eq m hm I Z hI hZ
  rw [← this, e1, e2]


/-- The quartic functional `G` in complex coordinates: `(1/16) ∑ g̃_{ijkl} ∏ (z + z̄)`, expanded as
the sum over all sign patterns of the monomials (blueprint (`bpW:w0n:Gz`)). -/
def quarticGComplex {N : ℕ} (m : ℝ) (hm : 0 < m) (z : Fin N → ℂ) : ℂ :=
  (1 / 16) * ∑ i, ∑ j, ∑ k, ∑ l, (normQuarticCoeff m hm i j k l : ℂ) *
    ∑ e : Bool × Bool × Bool × Bool, quarticMonomial z e i j k l

theorem sum_quarticMonomial {N : ℕ} (z : Fin N → ℂ) (i j k l : Fin N) :
    ∑ e : Bool × Bool × Bool × Bool, quarticMonomial z e i j k l
      = (z i + (starRingEnd ℂ) (z i)) * (z j + (starRingEnd ℂ) (z j))
        * (z k + (starRingEnd ℂ) (z k)) * (z l + (starRingEnd ℂ) (z l)) := by
  simp only [quarticMonomial, conjSelect, Fintype.sum_prod_type, Fintype.sum_bool, ite_true,
      ite_false,
    Bool.false_eq_true]
  ring

/-- `G(q) = quarticGComplex` for `z = (q + i p)/√2` (the coordinates of `bpW:w0:z`, `q_j =
(z_j + z̄_j)/√2`). -/
theorem quarticG_eq_complex {N : ℕ} (m : ℝ) (hm : 0 < m) (q p : Fin N → ℝ) :
    (quarticG m hm q : ℂ) =
      quarticGComplex m hm (fun j => ((q j : ℂ) + Complex.I * (p j : ℂ)) / (Real.sqrt 2 : ℂ)) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hz : ∀ j, ((q j : ℂ) + Complex.I * (p j : ℂ)) / (Real.sqrt 2 : ℂ)
      + (starRingEnd ℂ) (((q j : ℂ) + Complex.I * (p j : ℂ)) / (Real.sqrt 2 : ℂ))
      = (Real.sqrt 2 : ℂ) * (q j : ℂ) := by
    intro j
    simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    field_simp
    rw [hs2]
    ring
  unfold quarticGComplex quarticG
  simp only [sum_quarticMonomial, hz]
  push_cast
  have hl : ∀ j : Fin N, (Real.sqrt (lamMode m hm j) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (Real.sqrt_pos.2 (lamMode_pos m hm j)).ne'
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := hl i
  have := hl j
  have := hl k
  have := hl l
  unfold normQuarticCoeff
  push_cast
  have e4 : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2]; norm_num
  field_simp
  rw [e4]
  ring


end KAM.Wave

end
