/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Freq
public import KAM.CertificateSharp.Freq.QuadraticExact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# PlasmaLean's frequency

`ι = (75 + √5)/562` is the rotation number of PlasmaLean's example, a root of `281 x² - 75 x + 5`,
and `ω* = (ι, 1)` is the clock frequency of its canonical model. The infimum of `|k|₁ |k·ω*|` is
`ι = 0.13743…`, attained at `k = (1, 0)`. `isDiophantine_omegaStar` certifies the pair
`(γ*, 1)`, `γ* = 0.1374`, by `isDiophantine_of_quadCheck`, with kernel `decide` on the rational
data `iotaData`.

`iotaBox` is the frequency box of the small-divisor checker.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM KAM.Certificate KAM.CertificateSharp

/-- PlasmaLean's rotation number. -/
noncomputable def iota : ℝ := (75 + Real.sqrt 5) / 562

/-- The conjugate of `ι`. -/
noncomputable def iotaConj : ℝ := (75 - Real.sqrt 5) / 562

/-- The frequency `ω* = (ι, 1)`. -/
noncomputable def omegaStar : Fin 2 → ℝ := ![iota, 1]

/-- The Diophantine constant `γ* = 0.1374`. -/
def gammaStar : ℚ := 687 / 5000

/-- The rational data of the Diophantine pair. -/
def iotaData : QuadData where
  A := 281
  B := -75
  C := 5
  alo := 137430725938 / 10 ^ 12
  ahi := 137430725940 / 10 ^ 12
  blo := 129473188 / 10 ^ 9
  bhi := 129473189 / 10 ^ 9
  γ := gammaStar
  K0 := 3
  M2 := 1

theorem iotaData_check : iotaData.check = true := by decide +kernel

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_lo : (22360679774997 / 10 ^ 13 : ℝ) ≤ Real.sqrt 5 :=
  Real.le_sqrt_of_sq_le (by norm_num)

theorem sqrt5_hi : Real.sqrt 5 ≤ 22360679774998 / 10 ^ 13 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

theorem sqrt5_irrational : Irrational (Real.sqrt 5) := by
  simpa using Nat.Prime.irrational_sqrt Nat.prime_five

theorem irrational_comb (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Irrational ((75 + s * Real.sqrt 5) / 562) := by
  rintro ⟨q, hq⟩
  apply sqrt5_irrational
  have hs0 : (s : ℝ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨(562 * q - 75) / s, ?_⟩
  push_cast
  rw [hq]
  field_simp
  ring

theorem isDiophantine_omegaStar : IsDiophantine (gammaStar : ℝ) 1 omegaStar := by
  have h5 := sqrt5_sq
  have hl := sqrt5_lo
  have hh := sqrt5_hi
  have hi1 : Irrational iota := by simpa [iota] using irrational_comb 1 (Or.inl rfl)
  have hi2 : Irrational iotaConj := by
    have := irrational_comb (-1) (Or.inr rfl)
    simpa [iotaConj, sub_eq_add_neg] using this
  refine isDiophantine_of_quadCheck iotaData iotaData_check (α' := iotaConj) ?_ ?_ hi1 hi2 ?_ ?_ ?_ ?_
  · simp only [iotaData, iota, iotaConj]
    push_cast
    ring
  · simp only [iotaData, iota, iotaConj]
    push_cast
    linear_combination (-281 / 562 ^ 2 : ℝ) * h5
  · simp only [iotaData, iota]
    push_cast
    linarith
  · simp only [iotaData, iota]
    push_cast
    linarith
  · simp only [iotaData, iotaConj]
    push_cast
    linarith
  · simp only [iotaData, iotaConj]
    push_cast
    linarith

/-- The frequency box of `ι`. -/
def iotaBox : FreqBox := [(137430725939 / 10 ^ 12, 1 / 10 ^ 12)]

theorem iota_mem_box : FreqEncloses 1 iotaBox ![iota] := by
  have hl := sqrt5_lo
  have hh := sqrt5_hi
  intro i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [iotaBox, Matrix.cons_val_zero, iota]
  rw [abs_le]
  norm_num
  constructor <;> linarith

theorem snoc_iota : (Fin.snoc ![iota] 1 : Fin 2 → ℝ) = omegaStar := by
  funext i
  fin_cases i <;> simp [omegaStar, Fin.snoc]

end KAM.Sharp2.Examples

end
