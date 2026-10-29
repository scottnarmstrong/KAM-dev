/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Exact frequencies with proved rational boxes

The black box takes the exact reference vector `ω* : Fin n → ℝ`; the certificate stores only a
rational box (`FreqBox`), and `FreqEncloses n box ω` says `ω` lies in it.  The algebraic provider
`algFreq n coeffs x` has coordinates `Σ_j a_{ij} x^j` in `ℚ(x)`; `checkAlgBox` evaluates each
coordinate by rational interval arithmetic for `x ∈ [lo, hi]` and `algFreq_encloses` is its
soundness.
-/

@[expose] public section

namespace KAM.Certificate

/-- A rational frequency box: per coordinate `(centre, radius)`; it encloses `ω` when
`|ω_i - centre_i| ≤ radius_i` for every `i` (`FreqEncloses`). -/
abbrev FreqBox : Type := List (ℚ × ℚ)

/-- `ω` lies in the rational box. -/
def FreqEncloses (n : ℕ) (box : FreqBox) (ω : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, |ω i - ((box.getD i.val (0, 0)).1 : ℝ)| ≤ ((box.getD i.val (0, 0)).2 : ℝ)

/-- `ω_i = Σ_j a_{ij} x^j` for a real number `x`. -/
noncomputable def algFreq (n : ℕ) (coeffs : List (List ℚ)) (x : ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.range (coeffs.getD i.val []).length,
    (((coeffs.getD i.val []).getD j 0 : ℚ) : ℝ) * x ^ j

/-- Lower endpoint of `a x^j` for `x ∈ [lo, hi]`, `0 ≤ lo`. -/
def algTermLo (a lo hi : ℚ) (j : ℕ) : ℚ := if 0 ≤ a then a * lo ^ j else a * hi ^ j

/-- Upper endpoint of `a x^j` for `x ∈ [lo, hi]`, `0 ≤ lo`. -/
def algTermHi (a lo hi : ℚ) (j : ℕ) : ℚ := if 0 ≤ a then a * hi ^ j else a * lo ^ j

/-- Lower endpoint of `Σ_j a_j x^j`. -/
def algRowLo (as : List ℚ) (lo hi : ℚ) : ℚ :=
  ∑ j ∈ Finset.range as.length, algTermLo (as.getD j 0) lo hi j

/-- Upper endpoint of `Σ_j a_j x^j`. -/
def algRowHi (as : List ℚ) (lo hi : ℚ) : ℚ :=
  ∑ j ∈ Finset.range as.length, algTermHi (as.getD j 0) lo hi j

/-- Interval evaluation in `ℚ` of each `Σ_j a_{ij} x^j` for `x ∈ [lo, hi]` (`lo ≥ 0`), checked
inside the box; also `box.length = n`. -/
def checkAlgBox (n : ℕ) (coeffs : List (List ℚ)) (lo hi : ℚ) (box : FreqBox) : Bool :=
  decide (box.length = n) && decide (0 ≤ lo) &&
    (List.range n).all fun i =>
      decide ((box.getD i (0, 0)).1 - (box.getD i (0, 0)).2 ≤ algRowLo (coeffs.getD i []) lo hi) &&
      decide (algRowHi (coeffs.getD i []) lo hi ≤ (box.getD i (0, 0)).1 + (box.getD i (0, 0)).2)

private lemma algTerm_bounds {a lo hi : ℚ} {x : ℝ} (hlo : 0 ≤ lo) (hx : (lo : ℝ) ≤ x ∧ x ≤ hi)
    (j : ℕ) :
    (algTermLo a lo hi j : ℝ) ≤ (a : ℝ) * x ^ j ∧ (a : ℝ) * x ^ j ≤ (algTermHi a lo hi j : ℝ) := by
  have hl : (0 : ℝ) ≤ lo := by exact_mod_cast hlo
  have h1 : (lo : ℝ) ^ j ≤ x ^ j := pow_le_pow_left₀ hl hx.1 j
  have h2 : x ^ j ≤ (hi : ℝ) ^ j := pow_le_pow_left₀ (hl.trans hx.1) hx.2 j
  unfold algTermLo algTermHi
  by_cases ha : 0 ≤ a
  · have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    simp only [ha, ite_true]
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h1 ha', mul_le_mul_of_nonneg_left h2 ha'⟩
  · have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp ha).le
    simp only [ha, ite_false]
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h2 ha', mul_le_mul_of_nonpos_left h1 ha'⟩

theorem algFreq_encloses {n : ℕ} {coeffs : List (List ℚ)} {lo hi : ℚ} {box : FreqBox} {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ hi) (h : checkAlgBox n coeffs lo hi box = true) :
    FreqEncloses n box (algFreq n coeffs x) := by
  simp only [checkAlgBox, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨_, hlo⟩, hall⟩ := h
  intro i
  obtain ⟨h1, h2⟩ := hall i.val i.isLt
  have hb := fun j => algTerm_bounds (a := (coeffs.getD i.val []).getD j 0) hlo hx j
  have hL : ((algRowLo (coeffs.getD i.val []) lo hi : ℚ) : ℝ) ≤ algFreq n coeffs x i := by
    unfold algRowLo algFreq
    push_cast
    exact Finset.sum_le_sum fun j _ => (hb j).1
  have hH : algFreq n coeffs x i ≤ ((algRowHi (coeffs.getD i.val []) lo hi : ℚ) : ℝ) := by
    unfold algRowHi algFreq
    push_cast
    exact Finset.sum_le_sum fun j _ => (hb j).2
  have h1' : (((box.getD i.val (0, 0)).1 - (box.getD i.val (0, 0)).2 : ℚ) : ℝ) ≤
      (algRowLo (coeffs.getD i.val []) lo hi : ℚ) := by exact_mod_cast h1
  have h2' : ((algRowHi (coeffs.getD i.val []) lo hi : ℚ) : ℝ) ≤
      (((box.getD i.val (0, 0)).1 + (box.getD i.val (0, 0)).2 : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith

end KAM.Certificate
