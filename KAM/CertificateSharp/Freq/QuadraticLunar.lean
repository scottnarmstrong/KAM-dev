/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.QuadraticExact
public import KAM.Certificate.QuadraticDiophantine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Exact Diophantine constants of the lunar frequencies

With `g = (√5 - 1)/2` and `ν± = 1 ± 1/(40 + g)`, `quadCheck` certifies, by kernel `decide` on
the rational data of `QuadData`, the following constants (design §2.5), against the landed
`1/21` and `1/42`:

* `(ν±, 1)` is `(4923/100000, 1)`-Diophantine (infimum `2/(40 + g) = 0.049239`);
* `(ν± - 1, 1)` is `(2461/100000, 1)`-Diophantine (infimum `1/(40 + g) = 0.024620`).

`isDiophantine_smul` transfers a constant to a scaled vector.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate

/-- Scaling: `(γ, τ)`-Diophantine `ω` gives `(γ |c|^{-τ}...)`; here for `τ = 1` and `c ≠ 0`, the
vector `c • ω` is `(γ |c|, 1)`-Diophantine. -/
theorem isDiophantine_smul {n : ℕ} {γ : ℝ} {ω : Fin n → ℝ} (h : IsDiophantine γ 1 ω) (c : ℝ) :
    IsDiophantine (γ * |c|) 1 (fun i => c * ω i) := by
  intro k hk
  have := h k hk
  simp only [Real.rpow_one] at this ⊢
  have e : ∑ i, (k i : ℝ) * (c * ω i) = c * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, abs_mul, mul_div_right_comm, mul_comm |c|]
  exact mul_le_mul_of_nonneg_right this (abs_nonneg _)

private lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sqrt5_enc :
    (22360679774 / 10 ^ 10 : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 22360679775 / 10 ^ 10 := by
  have h0 := Real.sqrt_nonneg 5
  have h := sqrt5_sq
  constructor <;> nlinarith

private lemma sqrt5_irrational : Irrational (Real.sqrt 5) := by
  simpa using Nat.Prime.irrational_sqrt Nat.prime_five

private lemma irr_comb (m : ℤ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    Irrational ((m + e * Real.sqrt 5) / 3118) := by
  rintro ⟨q, hq⟩
  apply sqrt5_irrational
  have he0 : (e : ℝ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  refine ⟨(3118 * q - m) / e, ?_⟩
  push_cast
  rw [hq]
  field_simp
  ring

/-- Shared proof for the four lunar instances: roots `(m ± e√5)/3118`. -/
private theorem lunar_instance (d : QuadData) (hd : d.check = true) (m e : ℤ)
    (he : e = 1 ∨ e = -1) (hB : d.A * (2 * m) = -d.B * 3118)
    (hC : d.A * (m ^ 2 - 5) = d.C * 3118 ^ 2)
    (h1 : (d.alo : ℝ) ≤ (m + e * Real.sqrt 5) / 3118)
    (h2 : (m + e * Real.sqrt 5) / 3118 ≤ d.ahi)
    (h3 : (d.blo : ℝ) ≤ (m + -e * Real.sqrt 5) / 3118)
    (h4 : (m + -e * Real.sqrt 5) / 3118 ≤ d.bhi) :
    IsDiophantine (d.γ : ℝ) 1 ![(m + e * Real.sqrt 5) / 3118, 1] := by
  have hee : (e : ℝ) ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  refine isDiophantine_of_quadCheck d hd ?_ ?_ (irr_comb m e he) ?_ h1 h2 h3 h4
  · have : (d.A : ℝ) * (2 * m) = -d.B * 3118 := by exact_mod_cast hB
    linear_combination this / 3118
  · have : (d.A : ℝ) * (m ^ 2 - 5) = d.C * 3118 ^ 2 := by exact_mod_cast hC
    have h5 := sqrt5_sq
    linear_combination this / 3118 ^ 2 - (d.A : ℝ) * (e : ℝ) ^ 2 / 3118 ^ 2 * h5 -
      5 * (d.A : ℝ) / 3118 ^ 2 * hee
  · have := irr_comb m (-e) (by rcases he with rfl | rfl <;> simp)
    simpa [neg_mul] using this

/-- Rational data of the theta-frame frequency `ν₋`. -/
def lunarMinusThetaData : QuadData where
  A := 1559
  B := -3039
  C := 1481
  alo := (15206180339887 / 15590000000000 : ℚ)
  ahi := (1216494427191 / 1247200000000 : ℚ)
  blo := (1214705572809 / 1247200000000 : ℚ)
  bhi := (15183819660113 / 15590000000000 : ℚ)
  γ := (4923 / 100000 : ℚ)
  K0 := 2
  M2 := 3

theorem lunarMinusThetaData_check : lunarMinusThetaData.check = true := by decide +kernel

private theorem lunarMinusTheta_inst :
    IsDiophantine ((lunarMinusThetaData.γ : ℚ) : ℝ) 1
      ![((3039 : ℤ) + ((1 : ℤ) : ℝ) * Real.sqrt 5) / 3118, 1] := by
  obtain ⟨hl, hu⟩ := sqrt5_enc
  refine lunar_instance _ lunarMinusThetaData_check (3039 : ℤ) (1 : ℤ) (by norm_num)
    (by norm_num [lunarMinusThetaData]) (by norm_num [lunarMinusThetaData]) ?_ ?_ ?_ ?_ <;>
    · simp only [lunarMinusThetaData]
      push_cast
      rw [le_div_iff₀ (by norm_num)]
      nlinarith

/-- Rational data of the theta-frame frequency `ν₊`. -/
def lunarPlusThetaData : QuadData where
  A := 1559
  B := -3197
  C := 1639
  alo := (1277905572809 / 1247200000000 : ℚ)
  ahi := (15973819660113 / 15590000000000 : ℚ)
  blo := (15996180339887 / 15590000000000 : ℚ)
  bhi := (1279694427191 / 1247200000000 : ℚ)
  γ := (4923 / 100000 : ℚ)
  K0 := 2
  M2 := 3

theorem lunarPlusThetaData_check : lunarPlusThetaData.check = true := by decide +kernel

private theorem lunarPlusTheta_inst :
    IsDiophantine ((lunarPlusThetaData.γ : ℚ) : ℝ) 1
      ![((3197 : ℤ) + ((-1 : ℤ) : ℝ) * Real.sqrt 5) / 3118, 1] := by
  obtain ⟨hl, hu⟩ := sqrt5_enc
  refine lunar_instance _ lunarPlusThetaData_check (3197 : ℤ) (-1 : ℤ) (by norm_num)
    (by norm_num [lunarPlusThetaData]) (by norm_num [lunarPlusThetaData]) ?_ ?_ ?_ ?_ <;>
    · simp only [lunarPlusThetaData]
      push_cast
      rw [le_div_iff₀ (by norm_num)]
      nlinarith

/-- Rational data of the rot-frame frequency `ν₋`. -/
def lunarMinusRotData : QuadData where
  A := 1559
  B := 79
  C := 1
  alo := (-383819660113 / 15590000000000 : ℚ)
  ahi := (-30705572809 / 1247200000000 : ℚ)
  blo := (-32494427191 / 1247200000000 : ℚ)
  bhi := (-406180339887 / 15590000000000 : ℚ)
  γ := (2461 / 100000 : ℚ)
  K0 := 2
  M2 := 1

theorem lunarMinusRotData_check : lunarMinusRotData.check = true := by decide +kernel

private theorem lunarMinusRot_inst :
    IsDiophantine ((lunarMinusRotData.γ : ℚ) : ℝ) 1
      ![((-79 : ℤ) + ((1 : ℤ) : ℝ) * Real.sqrt 5) / 3118, 1] := by
  obtain ⟨hl, hu⟩ := sqrt5_enc
  refine lunar_instance _ lunarMinusRotData_check (-79 : ℤ) (1 : ℤ) (by norm_num)
    (by norm_num [lunarMinusRotData]) (by norm_num [lunarMinusRotData]) ?_ ?_ ?_ ?_ <;>
    · simp only [lunarMinusRotData]
      push_cast
      rw [le_div_iff₀ (by norm_num)]
      nlinarith

/-- Rational data of the rot-frame frequency `ν₊`. -/
def lunarPlusRotData : QuadData where
  A := 1559
  B := -79
  C := 1
  alo := (30705572809 / 1247200000000 : ℚ)
  ahi := (383819660113 / 15590000000000 : ℚ)
  blo := (406180339887 / 15590000000000 : ℚ)
  bhi := (32494427191 / 1247200000000 : ℚ)
  γ := (2461 / 100000 : ℚ)
  K0 := 2
  M2 := 1

theorem lunarPlusRotData_check : lunarPlusRotData.check = true := by decide +kernel

private theorem lunarPlusRot_inst :
    IsDiophantine ((lunarPlusRotData.γ : ℚ) : ℝ) 1
      ![((79 : ℤ) + ((-1 : ℤ) : ℝ) * Real.sqrt 5) / 3118, 1] := by
  obtain ⟨hl, hu⟩ := sqrt5_enc
  refine lunar_instance _ lunarPlusRotData_check (79 : ℤ) (-1 : ℤ) (by norm_num)
    (by norm_num [lunarPlusRotData]) (by norm_num [lunarPlusRotData]) ?_ ?_ ?_ ?_ <;>
    · simp only [lunarPlusRotData]
      push_cast
      rw [le_div_iff₀ (by norm_num)]
      nlinarith

/-- `(ν₋, 1)` is `(4923/100000, 1)`-Diophantine (landed: `1/21`). -/
theorem lunarNuMinus_isDiophantine_exact :
    IsDiophantine (4923 / 100000) 1 ![lunarNuMinus, 1] := by
  have := lunarMinusTheta_inst
  rw [lunarNuMinus_eq]
  simpa [lunarMinusThetaData] using this

/-- `(ν₊, 1)` is `(4923/100000, 1)`-Diophantine (landed: `1/21`). -/
theorem lunarNuPlus_isDiophantine_exact :
    IsDiophantine (4923 / 100000) 1 ![lunarNuPlus, 1] := by
  have := lunarPlusTheta_inst
  rw [lunarNuPlus_eq]
  have e : (3197 - Real.sqrt 5) / 3118 = ((3197 : ℤ) + (-1 : ℤ) * Real.sqrt 5) / 3118 := by
    push_cast; ring
  rw [e]
  simpa [lunarPlusThetaData] using this

/-- `(ν₋ - 1, 1)` is `(2461/100000, 1)`-Diophantine (landed: `1/42` after scaling by `1/2`). -/
theorem lunarNuMinus_sub_one_isDiophantine_exact :
    IsDiophantine (2461 / 100000) 1 ![lunarNuMinus - 1, 1] := by
  have := lunarMinusRot_inst
  have e : lunarNuMinus - 1 = ((-79 : ℤ) + (1 : ℤ) * Real.sqrt 5) / 3118 := by
    rw [lunarNuMinus_eq]; push_cast; ring
  rw [e]
  simpa [lunarMinusRotData] using this

/-- `(ν₊ - 1, 1)` is `(2461/100000, 1)`-Diophantine (landed: `1/42` after scaling by `1/2`). -/
theorem lunarNuPlus_sub_one_isDiophantine_exact :
    IsDiophantine (2461 / 100000) 1 ![lunarNuPlus - 1, 1] := by
  have := lunarPlusRot_inst
  have e : lunarNuPlus - 1 = ((79 : ℤ) + (-1 : ℤ) * Real.sqrt 5) / 3118 := by
    rw [lunarNuPlus_eq]; push_cast; ring
  rw [e]
  simpa [lunarPlusRotData] using this

end KAM.CertificateSharp
