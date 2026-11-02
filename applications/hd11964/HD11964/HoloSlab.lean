/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.Holo

/-!
# HD 11964: the Kepler contraction on per-slab strips (HD11964-HOLO)

The uniform strip `rhoHolo = (1/40, 3/20)` of `HD11964.Holo` is forced by the most eccentric slab
(cell 49, `ξ_c ≤ 0.1673`). On the slabs with smaller `ξ_c` the strip of planet `c` can be wider,
which is what the all-cells tail evaluation asks for (HD11964-HOLO handoff, the per-cell strips):

* slabs 0–4 (cells 0–45, `ξ_c ≤ 0.143097`): `ρ = (7/200, 3/20)`, `y = (1, 13/10)`,
  `κ = (23/25, 1/2)` (`keplerData_HD_A`);
* slab 5 (cells 46–48, `ξ_c ≤ 0.161123`): `ρ = (3/100, 3/20)`, `y = (9/10, 13/10)`,
  `κ = (47/50, 1/2)` (`keplerData_HD_B`);
* slab 6 (cell 49): the uniform `keplerData_HD` (`ρ_c = 1/40`).

`eccC_le_of_xi` bounds planet `c`'s ℓ¹ eccentricity vector on `|ξ_c| ≤ X` (with `|η_c| ≤ 1/500`,
`Λ_c ≥ Λ₀`) by `E` under two numerical conditions; `keplerData_of_ecc` turns an eccentricity bound
into `KAM.Kepler.KeplerData` under the two strip conditions.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real

namespace HD11964.Cover

/-! ### The eccentricity of planet `c` on a slab; the Kepler data from an eccentricity bound -/

/-- **Planet `c`'s ℓ¹ eccentricity on a slab** `|ξ| ≤ X`, `|η| ≤ 1/500`, `Λ ≥ Λ₀`: with
`G = (X² + (1/500)²)/2`, if `G ≤ Λ₀` and the quadratic `E²Λ² - (2G + 2X/500)Λ + G²` is
nonnegative and increasing at `Λ₀`, then `β(|ξ| + |η|) ≤ E`. -/
theorem eccC_le_of_xi {Λ ξ η X E Λ₀ : ℝ} (hΛ₀ : 0 < Λ₀) (hΛ : Λ₀ ≤ Λ) (hξ : |ξ| ≤ X)
    (hη : |η| ≤ 1 / 500) (hE : 0 ≤ E) (hG : (X ^ 2 + (1 / 500) ^ 2) / 2 ≤ Λ₀)
    (hf₀ : 0 ≤ E ^ 2 * Λ₀ ^ 2 - (X ^ 2 + (1 / 500) ^ 2 + 2 * X / 500) * Λ₀ +
      ((X ^ 2 + (1 / 500) ^ 2) / 2) ^ 2)
    (hf₁ : 0 ≤ 2 * E ^ 2 * Λ₀ - (X ^ 2 + (1 / 500) ^ 2 + 2 * X / 500)) :
    lpEccScale Λ ((ξ ^ 2 + η ^ 2) / 2) * (|ξ| + |η|) ≤ E := by
  have hΛp : 0 < Λ := hΛ₀.trans_le hΛ
  have hX : 0 ≤ X := (abs_nonneg ξ).trans hξ
  refine eccL1_le_of_sq hΛp hE ?_
  set Γ := (ξ ^ 2 + η ^ 2) / 2 with hΓdef
  have hΓ0 : 0 ≤ Γ := by positivity
  have hΓG : Γ ≤ (X ^ 2 + (1 / 500) ^ 2) / 2 := by
    have h1 : ξ ^ 2 ≤ X ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
    have h2 : η ^ 2 ≤ (1 / 500) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hη 2
    rw [hΓdef]; linarith
  have hcross : |ξ| * |η| ≤ X / 500 := by
    have := mul_le_mul hξ hη (abs_nonneg _) hX; linarith
  have hS : (|ξ| + |η|) ^ 2 ≤ 2 * Γ + 2 * X / 500 := by
    have : (|ξ| + |η|) ^ 2 = ξ ^ 2 + η ^ 2 + 2 * (|ξ| * |η|) := by
      rw [add_sq, sq_abs, sq_abs]; ring
    rw [this, hΓdef]; linarith
  have e1 : (1 - Γ / (2 * Λ)) / Λ = (2 * Λ - Γ) / (2 * Λ ^ 2) := by
    field_simp
  rw [e1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hA : 0 ≤ 2 * Λ - Γ := by linarith
  calc (2 * Λ - Γ) * (|ξ| + |η|) ^ 2 ≤ (2 * Λ - Γ) * (2 * Γ + 2 * X / 500) :=
        mul_le_mul_of_nonneg_left hS hA
    _ ≤ E ^ 2 * (2 * Λ ^ 2) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hΓG)
            (by linarith : (0 : ℝ) ≤ 2 * Λ - Γ - (X ^ 2 + (1 / 500) ^ 2) / 2),
          mul_nonneg hΓ0 hX, mul_nonneg (sub_nonneg.2 hΛ) hf₁,
          mul_nonneg (sq_nonneg E) (sq_nonneg (Λ - Λ₀))]

/-- **The Kepler data from an eccentricity bound**: if `β ≥ 0`, `β(|ξ| + |η|) ≤ E`,
`2πρ + E sinh y < y` and `E cosh y ≤ κ < 1`, the Kepler equation with the constant coefficients
`(βξ, βη)` has `KAM.Kepler.KeplerData` on `|Im λ| < 2πρ` with strip `y` and constant `κ`. -/
theorem keplerData_of_ecc {ρ y κ E β ξ η : ℝ} (hβ : 0 ≤ β) (he : β * (|ξ| + |η|) ≤ E)
    (hy : 0 < y) (hκ : κ < 1) (hinv : 2 * π * ρ + E * Real.sinh y < y)
    (hcon : E * Real.cosh y ≤ κ) :
    KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * ρ} (fun _ => ((β * ξ : ℝ) : ℂ))
      (fun _ => ((β * η : ℝ) : ℂ)) (fun lam => lam) y κ := by
  have hsum : |β * ξ| + |β * η| ≤ E := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, ← mul_add]; exact he
  refine ⟨isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const,
    analyticOnNhd_const, analyticOnNhd_const, analyticOnNhd_id, hy, hκ, ?_, ?_⟩
  · intro lam hlam
    simp only [Set.mem_ofPred_eq] at hlam
    simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, add_zero, zero_mul]
    have hs0 : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.2 hy.le
    have := mul_le_mul_of_nonneg_right hsum hs0
    linarith
  · intro lam _
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_right hsum (Real.cosh_pos y).le
    linarith

/-! ### Numerical bounds on `sinh`, `cosh` at `1` and `9/10` -/

theorem exp_one_bounds : Real.exp 1 ≤ 2.7183 :=
  (exp_bound_aux (lo := 2.7178) (by norm_num) (by norm_num [Finset.sum_range_succ,
    Nat.factorial])).2

theorem exp_neg_one_bounds : 0.3678 ≤ Real.exp (-1) ∧ Real.exp (-1) ≤ 0.3683 :=
  exp_bound_aux (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem exp_nine_tenths_le : Real.exp (9 / 10) ≤ 2.4597 :=
  (exp_bound_aux (lo := 2.4593) (by norm_num [abs_of_pos])
    (by norm_num [Finset.sum_range_succ, Nat.factorial])).2

theorem exp_neg_nine_tenths : 0.4065 ≤ Real.exp (-(9 / 10)) ∧ Real.exp (-(9 / 10)) ≤ 0.4068 :=
  exp_bound_aux (by norm_num [abs_of_neg]) (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem sinh_one_le : Real.sinh 1 ≤ 1.17525 := by
  rw [Real.sinh_eq]; linarith [exp_one_bounds, exp_neg_one_bounds.1]

theorem cosh_one_le : Real.cosh 1 ≤ 1.5433 := by
  rw [Real.cosh_eq]; linarith [exp_one_bounds, exp_neg_one_bounds.2]

theorem sinh_nine_tenths_le : Real.sinh (9 / 10) ≤ 1.0266 := by
  rw [Real.sinh_eq]; linarith [exp_nine_tenths_le, exp_neg_nine_tenths.1]

theorem cosh_nine_tenths_le : Real.cosh (9 / 10) ≤ 1.43325 := by
  rw [Real.cosh_eq]; linarith [exp_nine_tenths_le, exp_neg_nine_tenths.2]

/-! ### (1a) on the per-slab strips -/

/-- The strips on slabs 0–4 (cells 0–45): `ρ = (7/200, 3/20)`. -/
def rhoHoloA : Fin 2 → ℝ := ![7 / 200, 3 / 20]

/-- The Kepler strips on slabs 0–4: `y = (1, 13/10)`. -/
def yHoloA : Fin 2 → ℝ := ![1, 13 / 10]

/-- The contraction constants on slabs 0–4: `κ = (23/25, 1/2)`. -/
def kappaHoloA : Fin 2 → ℝ := ![23 / 25, 1 / 2]

/-- The strips on slab 5 (cells 46–48): `ρ = (3/100, 3/20)`. -/
def rhoHoloB : Fin 2 → ℝ := ![3 / 100, 3 / 20]

/-- The Kepler strips on slab 5: `y = (9/10, 13/10)`. -/
def yHoloB : Fin 2 → ℝ := ![9 / 10, 13 / 10]

/-- The contraction constants on slab 5: `κ = (47/50, 1/2)`. -/
def kappaHoloB : Fin 2 → ℝ := ![47 / 50, 1 / 2]

theorem lam_c_ge {w : Phase (2 + 2)} (hw : w ∈ holoDomHD) : (563 : ℝ) / 10000 ≤ fast w.2 0 := by
  have hΛlo := (hw.1.2.1 0).1
  simp only [lamLo, Fin.isValue, Matrix.cons_val_zero] at hΛlo
  norm_num at hΛlo; linarith

/-- Planet `c`'s eccentricity on `holoDomHD ∩ {|ξ_c| ≤ X}` from the numerical conditions at
`Λ₀ = 0.0563`. -/
theorem eccC_le_of_dom {w : Phase (2 + 2)} (hw : w ∈ holoDomHD) {X E : ℝ}
    (hξ : |slow w.1 0| ≤ X) (hE : 0 ≤ E) (hG : (X ^ 2 + (1 / 500) ^ 2) / 2 ≤ 563 / 10000)
    (hf₀ : 0 ≤ E ^ 2 * (563 / 10000) ^ 2 - (X ^ 2 + (1 / 500) ^ 2 + 2 * X / 500) * (563 / 10000)
      + ((X ^ 2 + (1 / 500) ^ 2) / 2) ^ 2)
    (hf₁ : 0 ≤ 2 * E ^ 2 * (563 / 10000) - (X ^ 2 + (1 / 500) ^ 2 + 2 * X / 500)) :
    lpEccScale (fast w.2 0) (lpGamma w 0) * (|slow w.1 0| + |slow w.2 0|) ≤ E :=
  eccC_le_of_xi (by norm_num) (lam_c_ge hw) hξ hw.2 hE hG hf₀ hf₁

/-- **(1a) on slabs 0–4** (`|ξ_c| ≤ 0.1431`, which contains the cells 0–45): the Kepler contraction
on `|Im λ_j| < 2πρ_j` with `ρ = (7/200, 3/20)`. Planet `c`: `ē_c = 0.59`, `y = 1`, `κ = 0.92`. -/
theorem keplerData_HD_A (j : Fin 2) {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hξ : |slow w.1 0| ≤ 1431 / 10000) :
    KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * rhoHoloA j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (yHoloA j) (kappaHoloA j) := by
  fin_cases j
  · have he := eccC_le_of_dom hw hξ (E := 59 / 100) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have hpi := Real.pi_lt_d2
    refine keplerData_of_ecc (Real.sqrt_nonneg _) he (by norm_num [yHoloA])
      (by norm_num [kappaHoloA]) ?_ ?_
    · simp only [rhoHoloA, yHoloA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      nlinarith [sinh_one_le]
    · simp only [yHoloA, kappaHoloA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      nlinarith [cosh_one_le]
  · simpa [rhoHoloA, rhoHolo, yHoloA, yHolo, kappaHoloA, kappaHolo] using keplerData_HD 1 hw

/-- **(1a) on slab 5** (`|ξ_c| ≤ 0.1612`, which contains the cells 46–48): the Kepler contraction
on `|Im λ_j| < 2πρ_j` with `ρ = (3/100, 3/20)`. Planet `c`: `ē_c = 0.65`, `y = 9/10`,
`κ = 0.94`. -/
theorem keplerData_HD_B (j : Fin 2) {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hξ : |slow w.1 0| ≤ 1612 / 10000) :
    KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * rhoHoloB j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (yHoloB j) (kappaHoloB j) := by
  fin_cases j
  · have he := eccC_le_of_dom hw hξ (E := 13 / 20) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have hpi := Real.pi_lt_d2
    refine keplerData_of_ecc (Real.sqrt_nonneg _) he (by norm_num [yHoloB])
      (by norm_num [kappaHoloB]) ?_ ?_
    · simp only [rhoHoloB, yHoloB, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      nlinarith [sinh_nine_tenths_le]
    · simp only [yHoloB, kappaHoloB, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      nlinarith [cosh_nine_tenths_le]
  · simpa [rhoHoloB, rhoHolo, yHoloB, yHolo, kappaHoloB, kappaHolo] using keplerData_HD 1 hw

end HD11964.Cover

end
