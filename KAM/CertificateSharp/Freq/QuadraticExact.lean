/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.QuadraticCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact quadratic Diophantine constants by finite enumeration plus the norm tail

`quadCheck` is a computable rational test. For `ω = (α, 1)` with `α` a root of
`A x² + B x + C` (conjugate `α'`) enclosed in rational intervals, a passing test with the
rational `γ` proves `IsDiophantine γ 1 ![α, 1]` (`isDiophantine_of_quadCheck`):

* *finite part*: all `(k₁, k₂)` with `|k₁| < K₀` and `|k₂| ≤ M₂` satisfy
  `γ ≤ (|k₁| + |k₂|) · lb|k₁α + k₂|` (interval lower bound); `|k₂| > M₂` forces
  `|k₁α + k₂| ≥ 1`;
* *tail*: `QuadraticCore.quad_tail_core` for `|k₁| ≥ K₀`.

The certified `γ` is the true infimum up to the enclosure (design §2.5). `isDiophantine_smul`
transfers the constant to a scaled vector `c • ω`.
-/

@[expose] public section

namespace KAM.CertificateSharp

/-- A rational lower bound of `|t|` for `t ∈ [u, v]`. -/
def lbAbs (u v : ℚ) : ℚ := if 0 < u then u else if v < 0 then -v else 0

theorem lbAbs_le {u v : ℚ} {t : ℝ} (hu : (u : ℝ) ≤ t) (hv : t ≤ v) : (lbAbs u v : ℝ) ≤ |t| := by
  unfold lbAbs
  split_ifs with h1 h2
  · have : (0 : ℝ) < u := by exact_mod_cast h1
    exact le_trans hu (le_abs_self t)
  · have : (v : ℝ) < 0 := by exact_mod_cast h2
    push_cast
    exact le_trans (by linarith) (neg_le_abs t)
  · push_cast
    exact abs_nonneg t

/-- A rational lower bound of `|k₁ α + k₂|` for `α ∈ [alo, ahi]`. -/
def quadLb (alo ahi : ℚ) (k1 k2 : ℤ) : ℚ :=
  if 0 ≤ k1 then lbAbs (k1 * alo + k2) (k1 * ahi + k2) else lbAbs (k1 * ahi + k2) (k1 * alo + k2)

theorem quadLb_le {alo ahi : ℚ} {α : ℝ} (h1 : (alo : ℝ) ≤ α) (h2 : α ≤ ahi) (k1 k2 : ℤ) :
    (quadLb alo ahi k1 k2 : ℝ) ≤ |k1 * α + k2| := by
  unfold quadLb
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ k1 := by exact_mod_cast hk
    refine lbAbs_le ?_ ?_ <;> push_cast <;> nlinarith
  · have hk' : (k1 : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hk).le
    refine lbAbs_le ?_ ?_ <;> push_cast <;> nlinarith

/-- The finite enumeration `|k₁| < K₀`, `|k₂| ≤ M₂`. -/
def quadFiniteOk (alo ahi γ : ℚ) (K0 M2 : ℕ) : Bool :=
  (List.range (2 * K0 - 1)).all fun i => (List.range (2 * M2 + 1)).all fun j =>
    (((i : ℤ) - (K0 - 1) == 0) && ((j : ℤ) - M2 == 0)) ||
      decide (γ ≤ (|(i : ℤ) - (K0 - 1)| + |(j : ℤ) - M2| : ℤ) *
        quadLb alo ahi ((i : ℤ) - (K0 - 1)) ((j : ℤ) - M2))

theorem quadFiniteOk_sound {alo ahi γ : ℚ} {K0 M2 : ℕ} (h : quadFiniteOk alo ahi γ K0 M2 = true)
    {k1 k2 : ℤ} (hk1 : |k1| < K0) (hk2 : |k2| ≤ M2) (hk : (k1, k2) ≠ (0, 0)) :
    γ ≤ (|k1| + |k2| : ℤ) * quadLb alo ahi k1 k2 := by
  unfold quadFiniteOk at h
  rw [List.all_eq_true] at h
  have hi := h (k1 + (K0 - 1)).toNat (by
    rw [List.mem_range]
    have := abs_lt.mp hk1
    omega)
  rw [List.all_eq_true] at hi
  have hj := hi (k2 + M2).toNat (by
    rw [List.mem_range]
    have := abs_le.mp hk2
    omega)
  have e1 : (((k1 + (K0 - 1)).toNat : ℕ) : ℤ) - (K0 - 1) = k1 := by
    have := abs_lt.mp hk1
    omega
  have e2 : (((k2 + M2).toNat : ℕ) : ℤ) - M2 = k2 := by
    have := abs_le.mp hk2
    omega
  rw [e1, e2] at hj
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hj
  rcases hj with ⟨h1, h2⟩ | hj
  · exact absurd (by rw [h1, h2]) hk
  · exact hj

/-- The rational data of the exact quadratic certificate. -/
structure QuadData where
  /-- The minimal polynomial `A x² + B x + C` of `α`. -/
  A : ℤ
  B : ℤ
  C : ℤ
  /-- Enclosures of `α` and of its conjugate `α'`. -/
  alo : ℚ
  ahi : ℚ
  blo : ℚ
  bhi : ℚ
  /-- The certified constant, the enumeration cut-off `K₀` and the row bound `M₂`. -/
  γ : ℚ
  K0 : ℕ
  M2 : ℕ

namespace QuadData

variable (d : QuadData)

/-- An upper bound of `|α - α'|`. -/
def D : ℚ := max (d.ahi - d.blo) (d.bhi - d.alo)

/-- A lower bound of `|α|`. -/
def a0 : ℚ := lbAbs d.alo d.ahi

/-- The row bound: `K₀ · max |α| ≤ M₂`. -/
def m2Ok : Bool := decide ((d.K0 : ℚ) * max |d.alo| |d.ahi| ≤ d.M2)

/-- The tail condition of the norm argument. -/
def tailOk : Bool :=
  decide (0 < 1 + d.a0 - d.A * d.γ * d.D) &&
    decide (d.γ * (1 + d.A * d.γ) ≤ (d.K0 : ℚ) ^ 2 * (1 + d.a0 - d.A * d.γ * d.D))

/-- The full rational test. -/
def check : Bool :=
  decide (0 < d.A) && decide (0 < d.γ) && decide (d.γ ≤ 1) && decide (1 ≤ d.K0) && d.tailOk && d.m2Ok &&
    quadFiniteOk d.alo d.ahi d.γ d.K0 d.M2

end QuadData

open QuadData in
/-- **Soundness of the exact quadratic certificate.** If `α` and its conjugate `α'` are
irrational roots of `A x² + B x + C` (Vieta form) inside the rational enclosures, a passing test
makes `(γ, 1)` a Diophantine pair for `(α, 1)`. -/
theorem isDiophantine_of_quadCheck (d : QuadData) (h : d.check = true) {α α' : ℝ}
    (hsum : (d.A : ℝ) * (α + α') = -d.B) (hprod : (d.A : ℝ) * (α * α') = d.C)
    (hαi : Irrational α) (hα'i : Irrational α')
    (h1 : (d.alo : ℝ) ≤ α) (h2 : α ≤ d.ahi) (h3 : (d.blo : ℝ) ≤ α') (h4 : α' ≤ d.bhi) :
    KAM.IsDiophantine (d.γ : ℝ) 1 ![α, 1] := by
  simp only [QuadData.check, QuadData.tailOk, QuadData.m2Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hA, hγ⟩, hγ1⟩, hK⟩, ⟨hpos, htail⟩⟩, hm2⟩, hfin⟩ := h
  have hA' : (0 : ℝ) < d.A := by exact_mod_cast hA
  have hγ' : (0 : ℝ) < d.γ := by exact_mod_cast hγ
  have hγ1' : (d.γ : ℝ) ≤ 1 := by exact_mod_cast hγ1
  have hK' : (1 : ℝ) ≤ d.K0 := by exact_mod_cast hK
  have hD : |α - α'| ≤ (d.D : ℝ) := by
    unfold QuadData.D
    push_cast
    rw [abs_le]
    constructor
    · have := le_max_right ((d.ahi : ℝ) - d.blo) ((d.bhi : ℝ) - d.alo)
      linarith
    · have := le_max_left ((d.ahi : ℝ) - d.blo) ((d.bhi : ℝ) - d.alo)
      linarith
  have ha0 : (d.a0 : ℝ) ≤ |α| := lbAbs_le h1 h2
  have hpos' : (0 : ℝ) < 1 + d.a0 - d.A * d.γ * d.D := by exact_mod_cast hpos
  have htail' : (d.γ : ℝ) * (1 + d.A * d.γ) ≤ (d.K0 : ℝ) ^ 2 * (1 + d.a0 - d.A * d.γ * d.D) := by
    exact_mod_cast htail
  intro k hk
  have key : (k 0, k 1) ≠ (0, 0) := by
    intro hk'
    apply hk
    ext i
    fin_cases i
    · simpa using congrArg Prod.fst hk'
    · simpa using congrArg Prod.snd hk'
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_one, mul_one]
  by_cases hk1 : (d.K0 : ℝ) ≤ |(k 0 : ℝ)|
  · exact quad_tail_core hA' hsum hprod hαi hα'i hD ha0 hγ' hK' hpos' htail' (k 0) (k 1) hk1
  · push Not at hk1
    have hk1z : |k 0| < d.K0 := by
      have : ((|k 0| : ℤ) : ℝ) < (d.K0 : ℤ) := by push_cast; exact hk1
      exact_mod_cast this
    have hs1 : (1 : ℝ) ≤ |(k 0 : ℝ)| + |(k 1 : ℝ)| := by
      have : (1 : ℤ) ≤ |k 0| + |k 1| := by
        by_contra hc
        apply key
        have a := abs_nonneg (k 0)
        have b := abs_nonneg (k 1)
        have : |k 0| = 0 := by omega
        have : |k 1| = 0 := by omega
        simp_all
      exact_mod_cast this
    have hs0 : (0 : ℝ) < |(k 0 : ℝ)| + |(k 1 : ℝ)| := by linarith
    by_cases hk2 : |k 1| ≤ d.M2
    · have := quadFiniteOk_sound hfin hk1z hk2 key
      have hlb := quadLb_le h1 h2 (k 0) (k 1)
      rw [div_le_iff₀ hs0]
      have e : ((|k 0| + |k 1| : ℤ) : ℝ) = |(k 0 : ℝ)| + |(k 1 : ℝ)| := by push_cast; rfl
      have h5 : (d.γ : ℝ) ≤ ((|k 0| + |k 1| : ℤ) : ℝ) * (quadLb d.alo d.ahi (k 0) (k 1) : ℝ) := by
        exact_mod_cast this
      rw [e] at h5
      calc (d.γ : ℝ) ≤ _ := h5
        _ ≤ |k 0 * α + k 1| * (|(k 0 : ℝ)| + |(k 1 : ℝ)|) := by
          have := mul_le_mul_of_nonneg_left hlb hs0.le
          linarith
    · push Not at hk2
      -- `|k₂| > M₂` forces `|k₁ α + k₂| ≥ 1`
      have hM : ((d.M2 : ℕ) : ℝ) + 1 ≤ |(k 1 : ℝ)| := by
        have : ((d.M2 + 1 : ℕ) : ℤ) ≤ |k 1| := by push_cast; omega
        have h6 : (((d.M2 + 1 : ℕ) : ℤ) : ℝ) ≤ ((|k 1| : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at h6
        exact h6
      have hamax : |α| ≤ ((max |d.alo| |d.ahi| : ℚ) : ℝ) := by
        push_cast
        exact abs_le_max_abs_abs h1 h2
      have hceil : (d.K0 : ℝ) * ((max |d.alo| |d.ahi| : ℚ) : ℝ) ≤ d.M2 := by
        have := hm2
        have h7 : (((d.K0 : ℚ) * max |d.alo| |d.ahi| : ℚ) : ℝ) ≤ ((d.M2 : ℕ) : ℚ) := by
          exact_mod_cast this
        push_cast at h7 ⊢
        exact h7
      have hamax0 : 0 ≤ ((max |d.alo| |d.ahi| : ℚ) : ℝ) := (abs_nonneg α).trans hamax
      have hk1le : |(k 0 : ℝ)| ≤ (d.K0 : ℝ) := hk1.le
      have h8 : |(k 0 : ℝ)| * |α| ≤ (d.K0 : ℝ) * ((max |d.alo| |d.ahi| : ℚ) : ℝ) :=
        mul_le_mul hk1le hamax (abs_nonneg _) (by positivity)
      have h9 : |(k 1 : ℝ)| - |(k 0 : ℝ) * α| ≤ |k 0 * α + k 1| := by
        have := abs_sub_abs_le_abs_sub (k 1 : ℝ) (-((k 0 : ℝ) * α))
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        exact this
      rw [abs_mul] at h9
      have hx1 : (1 : ℝ) ≤ |k 0 * α + k 1| := by linarith
      rw [div_le_iff₀ hs0]
      nlinarith
