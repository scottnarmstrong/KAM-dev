/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Constants
import KAM.Apost.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Constant inequalities of Part 2 (isoenergetic), proved once

Every inequality between the constants of `bpI:p2:constants` that the later modules of Part 2 use
is proved here, as an abstract statement about reals (the constants stay folded), so that no later
module unfolds a constant. They are grouped by the blueprint step that uses them; the steps are
those of `bpI:p2:constants`. All are in the namespace
`KAM.Iso.Apost.Arith`, and each statement has the exact shape that the corresponding estimate of
the blueprint produces.

* `co-xi0` (`sStar_arith`), `co-xi` (`xiN_arith`, `gL_arith`, `xiL_eq`, `xiN_le_hatCxi`,
  `xiL_le_hatCxi`, `hatCDK_arith`, `hatCDK_le_dStep`), `co-omega` (`dOmega_arith`,
  `Theta_sq_hatCS_le_dStep`), `co-dk` (`etaN_arith`, `dP_arith`, `dPxi_arith`);
* `ne-est` (`lin_arith`, `quad_le`, `E_total_arith`), `ne-energy` (`energy_total_arith`);
* `to-omega`, `to-row`, `to-avg`, `to-inv` (`to_omega_arith`, `to_row_arith`, `to_avg_arith`,
  `to_inv_arith`, `C_DT_small_of_CDTbord`);
* `st-small` (`iso_step_small`), `it-sums` and `it-stepsmall` (`iso_error_decay_hyp`,
  `iso_c_sum_small`, `iso_iteration_step_small`, `sum_coef_le_gen`, `iso_iteration_sums`,
  `iso_closeness_le`);
* `g1-e`, `g1-o` (`isoC1_pos`, `isoC2_pos`, `iso_g1_error_small`, `iso_g1_closeness_eq`).

The hypothesis `γ ≤ Θ` of the absorption lemmas is the conclusion of the frequency estimate
(`IsoAdmissible.freq`); the lemmas here take it as a hypothesis. They rest on the `KAM.Apost`
absorption
pack (`mul_rpow_le`, `div_absorb`, `absorb_mul_le`, `Correction.le_Theta_div`,
`Correction.rpow_add_one_le`, `Correction.xi0_arith`).
-/

public section

namespace KAM.Iso.Apost.Arith

open KAM.Apost

/-! ### Local facts on powers of `δ` -/

section Pow

variable {n : ℕ} {τ : ℝ} {δ : ℝ}

/-- `δ^a = δ^(κ+1) δ^(κ+1)` (`a = 2κ + 2`). -/
theorem rpow_aExp_eq (hδ : 0 < δ) :
    δ ^ aExp n τ = δ ^ (kappa n τ + 1) * δ ^ (kappa n τ + 1) := by
  rw [← Real.rpow_add hδ]
  congr 1
  unfold aExp
  ring

/-- `δ^(κ+2) = δ^(κ+1) δ`. -/
theorem rpow_kappa_add_two (hδ : 0 < δ) :
    δ ^ (kappa n τ + 2) = δ ^ (kappa n τ + 1) * δ := by
  rw [← Real.rpow_add_one hδ.ne']
  congr 1
  ring

/-- `(δ^a)^2 = δ^(2a)`. -/
theorem rpow_aExp_sq (hδ : 0 < δ) : (δ ^ aExp n τ) ^ 2 = δ ^ (2 * aExp n τ) := by
  rw [mul_comm, Real.rpow_mul hδ.le, Real.rpow_two]

end Pow

/-! ### Step `co-xi0`: the constants `ξ₀`, `ξ^ω` -/

section Correction

variable {n : ℕ} {τ M σK σB σT : ℝ} {γ δ ε : ℝ}

/-- Step `co-absorb`: `c ε/(γ δ^(κ+1)) ≤ Θ c ε/(γ² δ^a)` for `c ≥ 0`. -/
theorem absorb_kappa_succ (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) {c : ℝ}
    (hc : 0 ≤ c) :
    c * ε / (γ * δ ^ (kappa n τ + 1)) ≤
      Theta n M σK σB σT * c * ε / (γ ^ 2 * δ ^ aExp n τ) := by
  have hκ := one_le_kappa hP
  have h := absorb_mul_le (i := 1) (k := 2) (c := Theta n M σK σB σT * c)
    (j := kappa n τ + 1) (J := aExp n τ) hγ hγΘ hδ hδ1 (by norm_num)
    (by rw [aExp_eq]; linarith) hε hc (by simp)
  simpa only [pow_one] using h

/-- Step `co-xi0`, second entry:
`σ_T (|η^ω| + H_Y Γ H_N) ≤ (𝔪 Θ + 2 n c_R 𝔪⁵) ε/(γ δ^(κ+1))`, with `H_Y = 𝔪³`,
`H_N = 2 n 𝔪 ε`, `Γ = c_R γ⁻¹ δ^(-κ)`. -/
theorem sStar_second (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) {eω : ℝ} (heω0 : 0 ≤ eω) (heω : eω ≤ ε) :
    σT * (eω + mSize M σK σB σT ^ 3 * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) *
        (2 * n * mSize M σK σB σT * ε)) ≤
      (mSize M σK σB σT * Theta n M σK σB σT + 2 * n * cR n τ * mSize M σK σB σT ^ 5) * ε /
        (γ * δ ^ (kappa n τ + 1)) := by
  have hκ : 0 ≤ kappa n τ + 1 := by have := one_le_kappa hP; linarith
  have hD := Correction.gd_pos (j := kappa n τ + 1) hγ hδ
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hcR : (1 : ℝ) ≤ cR n τ := one_le_cR
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hσ0 : 0 ≤ σT := hP.σT_pos.le
  have hδκ : 0 < δ ^ kappa n τ := Real.rpow_pos_of_pos hδ _
  have hB : mSize M σK σB σT ^ 3 * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) *
      (2 * n * mSize M σK σB σT * ε) =
      2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε / (γ * δ ^ kappa n τ) := by
    rw [Real.rpow_neg hδ.le]
    field_simp
  have hle : γ * δ ^ (kappa n τ + 1) ≤ γ * δ ^ kappa n τ :=
    mul_le_mul_of_nonneg_left (Correction.rpow_add_one_le hδ hδ1) hγ.le
  have hBle : 2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε / (γ * δ ^ kappa n τ) ≤
      2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε / (γ * δ ^ (kappa n τ + 1)) :=
    div_le_div_of_nonneg_left (by positivity) hD hle
  have hBnn : 0 ≤ 2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε / (γ * δ ^ kappa n τ) := by
    positivity
  have h1 := Correction.le_Theta_div hγ hγΘ hδ hδ1 hκ hε
  have h2 : mSize M σK σB σT * ε ≤
      mSize M σK σB σT * (Theta n M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [hB]
  calc σT * (eω + 2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε / (γ * δ ^ kappa n τ))
      ≤ mSize M σK σB σT * (ε + 2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε /
          (γ * δ ^ kappa n τ)) :=
        mul_le_mul σT_le_mSize (by linarith) (by linarith) (by positivity)
    _ ≤ mSize M σK σB σT * ε + mSize M σK σB σT * (2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε /
          (γ * δ ^ (kappa n τ + 1))) := by
        rw [mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hBle (by positivity))
    _ ≤ mSize M σK σB σT * (Theta n M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) +
        mSize M σK σB σT * (2 * n * mSize M σK σB σT ^ 4 * cR n τ * ε /
          (γ * δ ^ (kappa n τ + 1))) := by linarith
    _ = _ := by ring

/-- Step `co-xi0`: `σ_T max {H_L + H_T Γ H_N, |η^ω| + H_Y Γ H_N} ≤ Ĉ_S ε/(γ δ^(κ+1))`, with
`H_L = 2 n 𝔪² ε`, `H_N = 2 n 𝔪 ε`, `H_T = C_T/δ`, `H_Y = 𝔪³`, `Γ = c_R γ⁻¹ δ^(-κ)`, `|η^ω| ≤ ε`
(the form of `border_solve` (c)). -/
theorem sStar_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) {eω : ℝ} (heω0 : 0 ≤ eω) (heω : eω ≤ ε) :
    σT * max (2 * n * mSize M σK σB σT ^ 2 * ε + C_T n M σK σB σT / δ *
          (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * (2 * n * mSize M σK σB σT * ε))
        (eω + mSize M σK σB σT ^ 3 * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) *
          (2 * n * mSize M σK σB σT * ε)) ≤
      hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by
  have hD := Correction.gd_pos (j := kappa n τ + 1) hγ hδ
  have hσ0 : 0 ≤ σT := hP.σT_pos.le
  have h1 := Correction.xi0_arith hP hγ hγΘ hδ hδ1 hε σT_le_mSize
  have h2 := sStar_second hP hγ hγΘ hδ hδ1 hε heω0 heω
  rw [mul_max_of_nonneg _ _ hσ0]
  refine max_le (h1.trans ?_) (h2.trans ?_)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right C_xi0_le_hatCS hε) hD.le
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right mSize_mul_Theta_add_le_hatCS hε) hD.le

/-! ### Step `co-xi`: `ξᴺ`, `gᴸ`, `ξᴸ`, `ξ`, `ΔK` -/

/-- Step `co-xi`: `|ξ₀| + Γ H_N ≤ Ĉ_{ξN} ε/(γ δ^(κ+1))` from `|ξ₀| ≤ Ĉ_S ε/(γ δ^(κ+1))`. -/
theorem xiN_arith (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) {x0 : ℝ}
    (hx0 : x0 ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) :
    x0 + cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * (2 * n * mSize M σK σB σT * ε) ≤
      hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by
  have hD := Correction.gd_pos (j := kappa n τ + 1) hγ hδ
  have hDκ := Correction.gd_pos (j := kappa n τ) hγ hδ
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hcR : (1 : ℝ) ≤ cR n τ := one_le_cR
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * (2 * n * mSize M σK σB σT * ε) =
      2 * n * mSize M σK σB σT * cR n τ * ε / (γ * δ ^ kappa n τ) := by
    have hδκ : 0 < δ ^ kappa n τ := Real.rpow_pos_of_pos hδ _
    rw [Real.rpow_neg hδ.le]
    field_simp
  have hle : γ * δ ^ (kappa n τ + 1) ≤ γ * δ ^ kappa n τ :=
    mul_le_mul_of_nonneg_left (Correction.rpow_add_one_le hδ hδ1) hγ.le
  have e2 : 2 * n * mSize M σK σB σT * cR n τ * ε / (γ * δ ^ kappa n τ) ≤
      2 * n * mSize M σK σB σT * cR n τ * ε / (γ * δ ^ (kappa n τ + 1)) :=
    div_le_div_of_nonneg_left (by positivity) hD hle
  rw [e1]
  calc _ ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) +
        2 * n * mSize M σK σB σT * cR n τ * ε / (γ * δ ^ (kappa n τ + 1)) := add_le_add hx0 e2
    _ = hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by
        unfold hatCxiN
        ring

/-- Step `co-xi`: `H_T (S + Γ H_N) + |ω| S + H_L ≤ Ĉ_g ε/(γ δ^(κ+2))` for
`S = Ĉ_S ε/(γ δ^(κ+1))` and `|ω| ≤ Θ` (the bound of `gᴸ` in `border_solve` (c)). -/
theorem gL_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) {w : ℝ}
    (hw : w ≤ Theta n M σK σB σT) :
    C_T n M σK σB σT / δ * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) +
        cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * (2 * n * mSize M σK σB σT * ε)) +
      w * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) +
      2 * n * mSize M σK σB σT ^ 2 * ε ≤
    hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := by
  have hκ : 0 ≤ kappa n τ + 2 := by have := one_le_kappa hP; linarith
  have hD := Correction.gd_pos (j := kappa n τ + 1) hγ hδ
  have hD2 := Correction.gd_pos (j := kappa n τ + 2) hγ hδ
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : 0 ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) :=
    div_nonneg (mul_nonneg (zero_le_one.trans (one_le_hatCS hP)) hε) hD.le
  have hxN := xiN_arith (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB) (σT := σT) hγ hδ hδ1 hε
    (le_refl (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))))
  have hCT : 0 ≤ C_T n M σK σB σT / δ :=
    div_nonneg (zero_le_one.trans (one_le_C_T hP)) hδ.le
  -- the term `H_T (S + Γ H_N)`
  have e1 : C_T n M σK σB σT / δ * (hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) =
      C_T n M σK σB σT * hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := by
    have hδκ : 0 < δ ^ (kappa n τ + 1) := Real.rpow_pos_of_pos hδ _
    rw [rpow_kappa_add_two hδ]
    field_simp
  have t1 := mul_le_mul_of_nonneg_left hxN hCT
  rw [e1] at t1
  -- the term `|ω| S`
  have hle2 : γ * δ ^ (kappa n τ + 2) ≤ γ * δ ^ (kappa n τ + 1) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) hγ.le
  have t2 : w * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) ≤
      Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := by
    calc w * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)))
        ≤ Theta n M σK σB σT * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) :=
          mul_le_mul_of_nonneg_right hw hS0
      _ = Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by ring
      _ ≤ Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_Theta hP))
              (zero_le_one.trans (one_le_hatCS hP))) hε) hD2 hle2
  -- the term `H_L`
  have h1 := Correction.le_Theta_div hγ hγΘ hδ hδ1 hκ hε
  have t3 : 2 * (n : ℝ) * mSize M σK σB σT ^ 2 * ε ≤
      2 * n * mSize M σK σB σT ^ 2 * (Theta n M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc _ ≤ C_T n M σK σB σT * hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) +
        Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) +
        2 * n * mSize M σK σB σT ^ 2 *
          (Theta n M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) := add_le_add (add_le_add t1 t2) t3
    _ = hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := by
        unfold hatCg
        ring

/-- Step `co-xi`: `Γ · c ε/(γ δ^(κ+2)) = c_R c ε/(γ² δ^a)` (used with `c = Ĉ_g`). -/
theorem xiL_eq (hγ : 0 < γ) (hδ : 0 < δ) (c : ℝ) :
    cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * (c * ε / (γ * δ ^ (kappa n τ + 2))) =
      cR n τ * c * ε / (γ ^ 2 * δ ^ aExp n τ) := by
  have hδκ : 0 < δ ^ kappa n τ := Real.rpow_pos_of_pos hδ _
  have hδκ2 : 0 < δ ^ (kappa n τ + 2) := Real.rpow_pos_of_pos hδ _
  have ha : δ ^ aExp n τ = δ ^ kappa n τ * δ ^ (kappa n τ + 2) := by
    rw [← Real.rpow_add hδ]
    congr 1
    rw [aExp_eq]
    ring
  rw [ha, Real.rpow_neg hδ.le]
  field_simp

/-- Step `co-xi`: `|ξᴸ| ≤ Γ Ĉ_g ε/(γ δ^(κ+2)) ≤ Ĉ_ξ ε/(γ² δ^a)`. -/
theorem xiL_le_hatCxi (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    cR n τ * γ⁻¹ * δ ^ (-kappa n τ) *
        (hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) ≤
      hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
  have hD : 0 < γ ^ 2 * δ ^ aExp n τ := mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hδ _)
  rw [xiL_eq hγ hδ]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right cR_mul_hatCg_le_hatCxi hε) hD.le

/-- Step `co-xi`: `|ξᴺ| ≤ Ĉ_{ξN} ε/(γ δ^(κ+1)) ≤ Ĉ_ξ ε/(γ² δ^a)` (absorbing `1/γ ≤ Θ/γ²`). -/
theorem xiN_le_hatCxi (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ≤
      hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
  have hD : 0 < γ ^ 2 * δ ^ aExp n τ := mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hδ _)
  refine (absorb_kappa_succ hP hγ hγΘ hδ hδ1 hε (zero_le_one.trans (one_le_hatCxiN hP))).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right Theta_mul_hatCxiN_le_hatCxi hε)
    hD.le

/-- Step `co-xi`: `2𝔪² · Ĉ_ξ ε/(γ² δ^a) = Ĉ_ΔK ε/(γ² δ^a)`. -/
theorem hatCDK_arith :
    2 * mSize M σK σB σT ^ 2 * (hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) =
      hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
  unfold hatCDK
  ring

/-- Step `co-xi`: `Ĉ_ΔK ε/(γ² δ^a) ≤ d`, `d = Ĉ_Δ ε/(γ² δ^a)`. -/
theorem hatCDK_le_dStep (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ≤ dStep n τ M σK σB σT γ ε δ :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hatCDK_le_hatCDelta hε)
    (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hδ _)).le

/-- Step `co-dxi`: `|ηᴺ| ≤ 2 n 𝔪 ε ≤ Ĉ_g ε/(γ δ^(κ+2))`. -/
theorem etaN_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    2 * n * mSize M σK σB σT * ε ≤
      hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := by
  have hκ : 0 ≤ kappa n τ + 2 := by have := one_le_kappa hP; linarith
  have hD2 := Correction.gd_pos (j := kappa n τ + 2) hγ hδ
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΘ := one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hCT : 0 ≤ C_T n M σK σB σT * hatCxiN n τ M σK σB σT :=
    mul_nonneg (zero_le_one.trans (one_le_C_T hP)) (zero_le_one.trans (one_le_hatCxiN hP))
  have hTS : 0 ≤ Theta n M σK σB σT * hatCS n τ M σK σB σT :=
    mul_nonneg (zero_le_one.trans hΘ) (zero_le_one.trans (one_le_hatCS hP))
  have h1 := Correction.le_Theta_div hγ hγΘ hδ hδ1 hκ hε
  have h2 : 2 * (n : ℝ) * mSize M σK σB σT ^ 2 * ε ≤
      2 * n * mSize M σK σB σT ^ 2 * (Theta n M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e : hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) =
      C_T n M σK σB σT * hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) +
      Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) +
        2 * n * mSize M σK σB σT ^ 2 *
          (Theta n M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) := by
    unfold hatCg
    ring
  have h3 : 0 ≤ C_T n M σK σB σT * hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) :=
    div_nonneg (mul_nonneg hCT hε) hD2.le
  have h3' : 0 ≤ Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) :=
    div_nonneg (mul_nonneg hTS hε) hD2.le
  have h4 : 2 * (n : ℝ) * mSize M σK σB σT * ε ≤ 2 * n * mSize M σK σB σT ^ 2 * ε := by
    have : 0 ≤ 2 * (n : ℝ) * mSize M σK σB σT * ε := by positivity
    have h5 : mSize M σK σB σT ≤ mSize M σK σB σT ^ 2 := by nlinarith
    calc 2 * (n : ℝ) * mSize M σK σB σT * ε
        = (2 * n * ε) * mSize M σK σB σT := by ring
      _ ≤ (2 * n * ε) * mSize M σK σB σT ^ 2 :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := by ring
  rw [e]
  linarith

/-! ### Step `co-omega`, `co-dk` -/

/-- Step `co-omega`: `|ω| |ξ^ω| ≤ Θ² Ĉ_S ε/(γ² δ^a)` for `|ω| ≤ Θ`, `|ξ^ω| ≤ Ĉ_S ε/(γ δ^(κ+1))`. -/
theorem dOmega_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) {w : ℝ}
    (hw : w ≤ Theta n M σK σB σT) :
    w * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) ≤
      Theta n M σK σB σT ^ 2 * hatCS n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
  have hD : 0 < γ * δ ^ (kappa n τ + 1) := Correction.gd_pos hγ hδ
  have hS0 : 0 ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) :=
    div_nonneg (mul_nonneg (zero_le_one.trans (one_le_hatCS hP)) hε) hD.le
  have hc : 0 ≤ Theta n M σK σB σT * hatCS n τ M σK σB σT :=
    mul_nonneg (zero_le_one.trans (one_le_Theta hP)) (zero_le_one.trans (one_le_hatCS hP))
  have h := absorb_kappa_succ hP hγ hγΘ hδ hδ1 hε hc
  calc w * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)))
      ≤ Theta n M σK σB σT * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) :=
        mul_le_mul_of_nonneg_right hw hS0
    _ = Theta n M σK σB σT * hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by ring
    _ ≤ Theta n M σK σB σT * (Theta n M σK σB σT * hatCS n τ M σK σB σT) * ε /
          (γ ^ 2 * δ ^ aExp n τ) := h
    _ = _ := by ring

/-- Step `co-omega`: `Θ² Ĉ_S ε/(γ² δ^a) ≤ d`, `d = Ĉ_Δ ε/(γ² δ^a)`. -/
theorem Theta_sq_hatCS_le_dStep (hγ : 0 < γ) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    Theta n M σK σB σT ^ 2 * hatCS n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ≤
      dStep n τ M σK σB σT γ ε δ :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right Theta_sq_mul_hatCS_le_hatCDelta hε)
    (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hδ _)).le

/-- Step `co-dk`: the bound of `∂_ω P`: `(𝔪² + n ε/δ) + (𝔪³ + C_X/δ) ≤ C_P/δ`
(`|∂_ω L| ≤ 𝔪² + n ε/δ`, `|∂_ω N| ≤ 𝔪³ + C_X/δ`, `|P| ≤ |L| + |N|`, `ε, δ ≤ 1`). -/
theorem dP_arith (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    mSize M σK σB σT ^ 2 + n * ε / δ + (mSize M σK σB σT ^ 3 + C_X n M σK σB σT / δ) ≤
      CP n M σK σB σT / δ := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hm2 : 0 ≤ mSize M σK σB σT ^ 2 := sq_nonneg _
  have hm3 : 0 ≤ mSize M σK σB σT ^ 3 := pow_nonneg (by linarith) 3
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [le_div_iff₀ hδ]
  have e : (mSize M σK σB σT ^ 2 + n * ε / δ + (mSize M σK σB σT ^ 3 + C_X n M σK σB σT / δ)) * δ =
      mSize M σK σB σT ^ 2 * δ + n * ε + mSize M σK σB σT ^ 3 * δ + C_X n M σK σB σT := by
    field_simp
    ring
  rw [e]
  have h1 : mSize M σK σB σT ^ 2 * δ ≤ mSize M σK σB σT ^ 2 := mul_le_of_le_one_right hm2 hδ1
  have h2 : mSize M σK σB σT ^ 3 * δ ≤ mSize M σK σB σT ^ 3 := mul_le_of_le_one_right hm3 hδ1
  have h3 : (n : ℝ) * ε ≤ n := mul_le_of_le_one_right hn hε1
  unfold CP
  linarith

/-- Step `co-dk`: `∂_ω ΔK = (∂_ω P) ξ + P ∂_ω ξ`:
`(C_P/δ) Ĉ_ξ ε/(γ² δ^a) + 2𝔪² Ĉ_g ε/(γ δ^(κ+2)) ≤ Ĉ_∂ ε/(γ² δ^(a+1))` (as `κ + 2 ≤ a + 1`). -/
theorem dPxi_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    CP n M σK σB σT / δ * (hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) +
        2 * mSize M σK σB σT ^ 2 *
          (hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) ≤
      hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1)) := by
  have hκ := one_le_kappa hP
  have hg0 := zero_le_one.trans (one_le_hatCg hP)
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have e1 : CP n M σK σB σT / δ * (hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) =
      CP n M σK σB σT * hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1)) := by
    have hδa : 0 < δ ^ aExp n τ := Real.rpow_pos_of_pos hδ _
    rw [Real.rpow_add_one hδ.ne']
    field_simp
  have e2 : 2 * mSize M σK σB σT ^ 2 *
        (hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) =
      (2 * mSize M σK σB σT ^ 2 * hatCg n τ M σK σB σT) * ε / (γ ^ 1 * δ ^ (kappa n τ + 2)) := by
    rw [pow_one]
    ring
  have h := absorb_mul_le (i := 1) (k := 2) (X := 2 * mSize M σK σB σT ^ 2 * hatCg n τ M σK σB σT)
    (c := 2 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT * hatCg n τ M σK σB σT)
    (j := kappa n τ + 2) (J := aExp n τ + 1) hγ hγΘ hδ hδ1 (by norm_num)
    (by rw [aExp_eq]; linarith) hε (by positivity)
    (by simp only [show (2 - 1 : ℕ) = 1 from rfl, pow_one]; exact le_of_eq (by ring))
  rw [e1, e2]
  calc _ ≤ CP n M σK σB σT * hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1)) +
        2 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT * hatCg n τ M σK σB σT * ε /
          (γ ^ 2 * δ ^ (aExp n τ + 1)) := add_le_add le_rfl h
    _ = hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1)) := by
        unfold hatCpartial
        ring

end Correction

/-! ### Steps `ne-est`, `ne-energy`: the new errors -/

section NewtonError

variable {n : ℕ} {τ M σK σB σT : ℝ} {γ δ ε : ℝ}

/-- Step `ne-est`: the three terms of `E_lin` add up to at most `Ĉ_lin ε²/(γ² δ^(a+1))`
(`2κ + 3 = a + 1` for the first two, `δ^(a+1) ≤ δ^a` for the third):
`|E_red| |ξ| + |E_sym| |∂_ω ξ| + |Ω_K| |ω| |ξ^ω|`. -/
theorem lin_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    C_red n M σK σB σT * ε / δ * (hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) +
      C_sym n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) *
        (hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) +
      C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) * Theta n M σK σB σT *
        (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) ≤
    hatClin n τ M σK σB σT * ε ^ 2 / (γ ^ 2 * δ ^ (aExp n τ + 1)) := by
  have hx : 0 < δ ^ (kappa n τ + 1) := Real.rpow_pos_of_pos hδ _
  have h1 : δ ^ (aExp n τ + 1) = δ ^ aExp n τ * δ := Real.rpow_add_one hδ.ne' _
  have h2 := rpow_aExp_eq (n := n) (τ := τ) hδ
  have h3 := rpow_kappa_add_two (n := n) (τ := τ) hδ
  have hΘ := zero_le_one.trans (one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT))
  have hΩ := zero_le_one.trans (one_le_C_Omega hP (n := n) (τ := τ) (M := M) (σK := σK)
    (σB := σB) (σT := σT))
  have hS := zero_le_one.trans (one_le_hatCS hP)
  rw [h1, h3, h2]
  generalize δ ^ (kappa n τ + 1) = x at hx ⊢
  have e12 : C_red n M σK σB σT * ε / δ * (hatCxi n τ M σK σB σT * ε / (γ ^ 2 * (x * x))) +
      C_sym n τ M σK σB σT * ε / (γ * x) *
        (hatCg n τ M σK σB σT * ε / (γ * (x * δ))) =
      (C_red n M σK σB σT * hatCxi n τ M σK σB σT +
        C_sym n τ M σK σB σT * hatCg n τ M σK σB σT) * ε ^ 2 / (γ ^ 2 * (x * x * δ)) := by
    field_simp
  have e3 : C_Omega n τ M σK σB σT * ε / (γ * x) * Theta n M σK σB σT *
      (hatCS n τ M σK σB σT * ε / (γ * x)) =
      Theta n M σK σB σT * C_Omega n τ M σK σB σT * hatCS n τ M σK σB σT * ε ^ 2 /
        (γ ^ 2 * (x * x)) := by
    field_simp
  have hD : 0 < γ ^ 2 * (x * x * δ) := by positivity
  have hle : γ ^ 2 * (x * x * δ) ≤ γ ^ 2 * (x * x) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_of_le_one_right (by positivity) hδ1
  have h3le : Theta n M σK σB σT * C_Omega n τ M σK σB σT * hatCS n τ M σK σB σT * ε ^ 2 /
        (γ ^ 2 * (x * x)) ≤
      Theta n M σK σB σT * C_Omega n τ M σK σB σT * hatCS n τ M σK σB σT * ε ^ 2 /
        (γ ^ 2 * (x * x * δ)) :=
    div_le_div_of_nonneg_left (by positivity) hD hle
  rw [e12, e3]
  calc _ ≤ (C_red n M σK σB σT * hatCxi n τ M σK σB σT +
        C_sym n τ M σK σB σT * hatCg n τ M σK σB σT) * ε ^ 2 / (γ ^ 2 * (x * x * δ)) +
      Theta n M σK σB σT * C_Omega n τ M σK σB σT * hatCS n τ M σK σB σT * ε ^ 2 /
        (γ ^ 2 * (x * x * δ)) := add_le_add le_rfl h3le
    _ = _ := by
        unfold hatClin
        ring

/-- Step `ne-total`: `M (Ĉ_ΔK ε/(γ² δ^a))² ≤ 𝔪 Ĉ_ΔK² ε²/(γ⁴ δ^(2a))`, the bound of
`|Δ²X|` and `|Δ²H|` (`M ≤ 𝔪`, `M/2 ≤ 𝔪`). -/
theorem quad_le (hγ : 0 < γ) (hδ : 0 < δ) :
    M * (hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) ^ 2 ≤
      mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2 * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) := by
  have hγδ : 0 < γ ^ 4 * δ ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hδ _)
  have : (hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) ^ 2 =
      hatCDK n τ M σK σB σT ^ 2 * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) := by
    rw [div_pow, mul_pow, mul_pow, ← pow_mul, rpow_aExp_sq hδ]
  rw [this, ← mul_div_assoc, mul_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right M_le_mSize (by positivity))
    hγδ.le

/-- Step `ne-est`: `|P| |S⁻¹| |E_lin| + |Δ²X| + |ξ^ω| |∂_ω ΔK| ≤ Ĉ_E1 ε²/(γ⁴ δ^(2a))`, given
`|P| ≤ 2𝔪²`, `|S⁻¹| ≤ 2`, `|E_lin| ≤ Ĉ_lin ε²/(γ² δ^(a+1))`, `|Δ²X| ≤ M |ΔK|²`,
`|ΔK| ≤ Ĉ_ΔK ε/(γ² δ^a)`, `|ξ^ω| ≤ Ĉ_S ε/(γ δ^(κ+1))`, `|∂_ω ΔK| ≤ Ĉ_∂ ε/(γ² δ^(a+1))`
(uses `γ² δ^(a-1) ≤ Θ²` and `γ δ^(a-κ-2) ≤ Θ`). -/
theorem E_total_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * mSize M σK σB σT ^ 2 *
        (2 * (hatClin n τ M σK σB σT * ε ^ 2 / (γ ^ 2 * δ ^ (aExp n τ + 1)))) +
      M * (hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) ^ 2 +
      hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) *
        (hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1))) ≤
    hatCE1 n τ M σK σB σT * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) := by
  have ha := eight_le_aExp hP
  have hκ := one_le_kappa hP
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have hlin := zero_le_one.trans (one_le_hatClin hP)
  have hS := zero_le_one.trans (one_le_hatCS hP)
  have hpar := zero_le_one.trans (one_le_hatCpartial hP)
  have hΘ := zero_le_one.trans (one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT))
  -- the linear term
  have hX : 0 ≤ 4 * mSize M σK σB σT ^ 2 * hatClin n τ M σK σB σT := by positivity
  have hlinear := absorb_mul_le (i := 2) (k := 4) (j := aExp n τ + 1) (J := 2 * aExp n τ)
    (c := 4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 * hatClin n τ M σK σB σT)
    (ε := ε ^ 2) hγ hγΘ hδ hδ1 (by norm_num) (by linarith) (sq_nonneg ε) hX
    (by simp only [show (4 - 2 : ℕ) = 2 from rfl]; exact le_of_eq (by ring))
  have hlinear' : 2 * mSize M σK σB σT ^ 2 *
        (2 * (hatClin n τ M σK σB σT * ε ^ 2 / (γ ^ 2 * δ ^ (aExp n τ + 1)))) =
      4 * mSize M σK σB σT ^ 2 * hatClin n τ M σK σB σT * ε ^ 2 /
        (γ ^ 2 * δ ^ (aExp n τ + 1)) := by ring
  -- the `ξ^ω ∂_ω ΔK` term
  have hCe : hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) *
        (hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1))) =
      (hatCS n τ M σK σB σT * hatCpartial n τ M σK σB σT) * ε ^ 2 /
        (γ ^ 3 * δ ^ (kappa n τ + 1 + (aExp n τ + 1))) := by
    have h1 : 0 < δ ^ (kappa n τ + 1) := Real.rpow_pos_of_pos hδ _
    have h2 : 0 < δ ^ (aExp n τ + 1) := Real.rpow_pos_of_pos hδ _
    rw [Real.rpow_add hδ (kappa n τ + 1) (aExp n τ + 1)]
    field_simp
  have hcross := absorb_mul_le (i := 3) (k := 4) (j := kappa n τ + 1 + (aExp n τ + 1))
    (J := 2 * aExp n τ)
    (X := hatCS n τ M σK σB σT * hatCpartial n τ M σK σB σT)
    (c := Theta n M σK σB σT * hatCS n τ M σK σB σT * hatCpartial n τ M σK σB σT)
    (ε := ε ^ 2) hγ hγΘ hδ hδ1 (by norm_num) (by rw [aExp_eq]; linarith) (sq_nonneg ε)
    (mul_nonneg hS hpar)
    (by simp only [show (4 - 3 : ℕ) = 1 from rfl, pow_one]; exact le_of_eq (by ring))
  have hE : hatCE1 n τ M σK σB σT * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) =
      4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 * hatClin n τ M σK σB σT * ε ^ 2 /
        (γ ^ 4 * δ ^ (2 * aExp n τ)) +
      mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2 * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) +
      Theta n M σK σB σT * hatCS n τ M σK σB σT * hatCpartial n τ M σK σB σT * ε ^ 2 /
        (γ ^ 4 * δ ^ (2 * aExp n τ)) := by
    unfold hatCE1
    ring
  rw [hE, hlinear', hCe]
  exact add_le_add (add_le_add hlinear (quad_le hγ hδ)) hcross

/-- Step `ne-energy`: `|D(H∘K)| |ξᴸ| + M |ΔK|² ≤ Ĉ_E2 ε²/(γ⁴ δ^(2a))`, with
`|D(H∘K)| ≤ n (2 n 𝔪 ε + Θ C_Ω ε/(γ δ^(κ+1)))` (energy-approx (f)), `|ξᴸ| ≤ c_R Ĉ_g ε/(γ² δ^a)`
(uses `γ δ^(κ+1) ≤ Θ`). -/
theorem energy_total_arith (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    ((n : ℝ) * (2 * n * mSize M σK σB σT * ε +
        Theta n M σK σB σT * (C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))))) *
      (cR n τ * hatCg n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) +
      M * (hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) ^ 2 ≤
    hatCE2 n τ M σK σB σT * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) := by
  have ha := eight_le_aExp hP
  have hκ := one_le_kappa hP
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have hn := hP.one_le_cast
  have hΘ := zero_le_one.trans (one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT))
  have hΩ := zero_le_one.trans (one_le_C_Omega hP (n := n) (τ := τ) (M := M) (σK := σK)
    (σB := σB) (σT := σT))
  have hg := zero_le_one.trans (one_le_hatCg hP)
  have hcR := zero_le_one.trans (one_le_cR (n := n) (τ := τ))
  have hD1 : 0 < γ * δ ^ (kappa n τ + 1) := Correction.gd_pos hγ hδ
  have hD2 : 0 < γ ^ 2 * δ ^ aExp n τ := mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hδ _)
  -- `|D(H∘K)| ≤ n Θ (2 n 𝔪 + C_Ω) ε/(γ δ^(κ+1))`
  have h1 := Correction.le_Theta_div hγ hγΘ hδ hδ1 (j := kappa n τ + 1)
    (by linarith) hε
  have hA : (n : ℝ) * (2 * n * mSize M σK σB σT * ε +
        Theta n M σK σB σT * (C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)))) ≤
      (n * Theta n M σK σB σT * (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT)) * ε /
        (γ * δ ^ (kappa n τ + 1)) := by
    calc (n : ℝ) * (2 * n * mSize M σK σB σT * ε +
          Theta n M σK σB σT * (C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))))
        = (2 * n ^ 2 * mSize M σK σB σT) * ε +
          n * Theta n M σK σB σT * C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by
          ring
      _ ≤ (2 * n ^ 2 * mSize M σK σB σT) * (Theta n M σK σB σT * ε /
            (γ * δ ^ (kappa n τ + 1))) +
          n * Theta n M σK σB σT * C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl
      _ = _ := by ring
  have hX0 : 0 ≤ cR n τ * hatCg n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) :=
    div_nonneg (mul_nonneg (mul_nonneg hcR hg) hε) hD2.le
  have hprod := mul_le_mul_of_nonneg_right hA hX0
  have hBX : (n * Theta n M σK σB σT * (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT)) *
        ε / (γ * δ ^ (kappa n τ + 1)) *
        (cR n τ * hatCg n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) =
      (n * Theta n M σK σB σT * (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT) *
        cR n τ * hatCg n τ M σK σB σT) * ε ^ 2 /
        (γ ^ 3 * δ ^ (kappa n τ + 1 + aExp n τ)) := by
    have h1 : 0 < δ ^ (kappa n τ + 1) := Real.rpow_pos_of_pos hδ _
    have h2 : 0 < δ ^ aExp n τ := Real.rpow_pos_of_pos hδ _
    rw [Real.rpow_add hδ (kappa n τ + 1) (aExp n τ)]
    field_simp
  have hcross := absorb_mul_le (i := 3) (k := 4) (j := kappa n τ + 1 + aExp n τ)
    (J := 2 * aExp n τ)
    (X := n * Theta n M σK σB σT * (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT) *
      cR n τ * hatCg n τ M σK σB σT)
    (c := Theta n M σK σB σT * (n * Theta n M σK σB σT *
      (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT) *
      cR n τ * hatCg n τ M σK σB σT))
    (ε := ε ^ 2) hγ hγΘ hδ hδ1 (by norm_num) (by rw [aExp_eq]; linarith) (sq_nonneg ε)
    (by positivity)
    (by simp only [show (4 - 3 : ℕ) = 1 from rfl, pow_one]; exact le_refl _)
  have hE : hatCE2 n τ M σK σB σT * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) =
      Theta n M σK σB σT * (n * Theta n M σK σB σT *
        (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT) *
        cR n τ * hatCg n τ M σK σB σT) * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) +
      mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2 * ε ^ 2 / (γ ^ 4 * δ ^ (2 * aExp n τ)) := by
    unfold hatCE2
    ring
  rw [hE]
  rw [hBX] at hprod
  exact add_le_add (hprod.trans hcross) (quad_le hγ hδ)

end NewtonError

/-! ### Steps `to-omega`, `to-row`, `to-avg`, `to-inv`: the new extended torsion -/

section Torsion

variable {n : ℕ} {τ M σK σB σT : ℝ} {δ d : ℝ}

/-- Step `to-omega`: `|N̄ᵀ| ≤ 4 n 𝔪²` times `n d 2𝔪²/δ` is `8 n² 𝔪⁴ d/δ`. -/
theorem to_omega_arith {a b : ℝ} (hδ : 0 < δ) (hb0 : 0 ≤ b) (ha : a ≤ 4 * n * mSize M σK σB σT ^ 2)
    (hb : b ≤ n * d * (2 * mSize M σK σB σT ^ 2) / δ) :
    a * b ≤ 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  calc a * b ≤ (4 * n * mSize M σK σB σT ^ 2) * (n * d * (2 * mSize M σK σB σT ^ 2) / δ) :=
        mul_le_mul ha hb hb0 (by positivity)
    _ = _ := by
        field_simp
        ring

/-- Step `to-row`: `n (M d 2𝔪² + M C_ΔN d/δ) ≤ C_Y d/δ` for `d ≥ 0`, `δ ≤ 1`, `M ≤ 𝔪`. -/
theorem to_row_arith (hP : Params n τ M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 ≤ d) :
    (n : ℝ) * (M * d * (2 * mSize M σK σB σT ^ 2) +
        M * (C_DN n M σK σB σT * d / δ)) ≤ CY n M σK σB σT * d / δ := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hn := hP.one_le_cast
  have hDN := zero_le_one.trans (one_le_C_DN hP)
  have hdδ : d ≤ d / δ := (le_div_iff₀ hδ).2 (mul_le_of_le_one_right hd hδ1)
  have t1 : M * d * (2 * mSize M σK σB σT ^ 2) ≤
      mSize M σK σB σT * (d / δ) * (2 * mSize M σK σB σT ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul M_le_mSize hdδ hd (by linarith)
  have t2 : M * (C_DN n M σK σB σT * d / δ) ≤ mSize M σK σB σT * (C_DN n M σK σB σT * d / δ) :=
    mul_le_mul_of_nonneg_right M_le_mSize (by positivity)
  calc (n : ℝ) * (M * d * (2 * mSize M σK σB σT ^ 2) + M * (C_DN n M σK σB σT * d / δ))
      ≤ n * (mSize M σK σB σT * (d / δ) * (2 * mSize M σK σB σT ^ 2) +
        mSize M σK σB σT * (C_DN n M σK σB σT * d / δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add t1 t2) (by linarith)
    _ = CY n M σK σB σT * d / δ := by
        unfold CY
        ring

/-- Step `to-avg`: `max {C_ΔT d/δ² + 8n²𝔪⁴ d/δ + d, C_Y d/δ} ≤ C_{Δ𝖳} d/δ²` (`δ ≤ 1`). -/
theorem to_avg_arith (hP : Params n τ M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 ≤ d) :
    max (C_DT n M σK σB σT * d / δ ^ 2 + 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ + d)
        (CY n M σK σB σT * d / δ) ≤ CDTbord n M σK σB σT * d / δ ^ 2 := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hδδ : δ ^ 2 ≤ δ := by
    calc δ ^ 2 = δ * δ := sq δ
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ.le
      _ = δ := mul_one δ
  have hCY := zero_le_one.trans (one_le_CY hP)
  have h1 : 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ ≤
      8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hδ2 hδδ
  have h2 : d ≤ d / δ ^ 2 := (le_div_iff₀ hδ2).2 (by nlinarith)
  have h3 : CY n M σK σB σT * d / δ ≤ CY n M σK σB σT * d / δ ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg hCY hd) hδ2 hδδ
  have e : CDTbord n M σK σB σT * d / δ ^ 2 =
      C_DT n M σK σB σT * d / δ ^ 2 + 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ ^ 2 +
        d / δ ^ 2 + CY n M σK σB σT * d / δ ^ 2 := by
    unfold CDTbord
    ring
  have hDT : 0 ≤ C_DT n M σK σB σT * d / δ ^ 2 :=
    div_nonneg (mul_nonneg (zero_le_one.trans (one_le_C_DT hP)) hd) hδ2.le
  have h8 : 0 ≤ 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ ^ 2 := by positivity
  have hdd : 0 ≤ d / δ ^ 2 := div_nonneg hd hδ2.le
  have h3' : 0 ≤ CY n M σK σB σT * d / δ ^ 2 := div_nonneg (mul_nonneg hCY hd) hδ2.le
  rw [e]
  refine max_le ?_ ?_
  · linarith
  · linarith

/-- Step `to-inv`: with `‖Δ𝒯‖ ≤ C_{Δ𝖳} d/δ²` and `2𝔪 C_{Δ𝖳} d/δ² ≤ 1`: `σ_T ‖Δ𝒯‖ ≤ 1/2` and
`2 σ_T² ‖Δ𝒯‖ ≤ 2𝔪² C_{Δ𝖳} d/δ²`. -/
theorem to_inv_arith (hP : Params n τ M σK σB σT) {Δn : ℝ} (hΔ0 : 0 ≤ Δn)
    (hΔ : Δn ≤ CDTbord n M σK σB σT * d / δ ^ 2)
    (hsmall : 2 * mSize M σK σB σT * CDTbord n M σK σB σT * d / δ ^ 2 ≤ 1) :
    σT * Δn ≤ 1 / 2 ∧
      2 * σT ^ 2 * Δn ≤ 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * d / δ ^ 2 := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  have hσ0 := hP.σT_pos.le
  have hσ : σT ≤ mSize M σK σB σT := σT_le_mSize
  have e1 : 2 * mSize M σK σB σT * CDTbord n M σK σB σT * d / δ ^ 2 =
      2 * (mSize M σK σB σT * (CDTbord n M σK σB σT * d / δ ^ 2)) := by ring
  have e2 : 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * d / δ ^ 2 =
      2 * mSize M σK σB σT ^ 2 * (CDTbord n M σK σB σT * d / δ ^ 2) := by ring
  refine ⟨?_, ?_⟩
  · calc σT * Δn ≤ mSize M σK σB σT * Δn := mul_le_mul_of_nonneg_right hσ hΔ0
      _ ≤ mSize M σK σB σT * (CDTbord n M σK σB σT * d / δ ^ 2) :=
          mul_le_mul_of_nonneg_left hΔ (by linarith)
      _ ≤ 1 / 2 := by linarith
  · rw [e2]
    have h2 : σT ^ 2 ≤ mSize M σK σB σT ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    calc 2 * σT ^ 2 * Δn ≤ 2 * mSize M σK σB σT ^ 2 * Δn :=
          mul_le_mul_of_nonneg_right (by linarith) hΔ0
      _ ≤ _ := mul_le_mul_of_nonneg_left hΔ (by positivity)

/-- Step `to-frame`: the smallness `2𝔪 C_{Δ𝖳} d/δ² ≤ 1` implies the smallness
`2𝔪 C_ΔT d/δ² ≤ 1` of `perturbation_noA5` (`C_ΔT ≤ C_{Δ𝖳}`). -/
theorem C_DT_small_of_CDTbord (hP : Params n τ M σK σB σT) (hδ : 0 < δ) (hd : 0 ≤ d)
    (h : 2 * mSize M σK σB σT * CDTbord n M σK σB σT * d / δ ^ 2 ≤ 1) :
    2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1 := by
  have hm : (1 : ℝ) ≤ mSize M σK σB σT := one_le_mSize
  refine le_trans (div_le_div_of_nonneg_right ?_ (pow_pos hδ 2).le) h
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (C_DT_le_CDTbord hP) (by linarith)) hd

end Torsion

/-! ### Step `st-small`: smallness of the isoenergetic step -/

section Step

variable {n : ℕ} {τ M σK σB σT : ℝ} {γ δ ε β : ℝ}

theorem two_pow_mul_le_aux {Θ X Y : ℝ} {p : ℕ} (hΘ : 1 ≤ Θ) (hp : p ≤ 3) (hX : 0 ≤ X)
    (hXY : X ≤ Y) : 2 * Θ ^ p * X ≤ 2 * Θ ^ 3 * Y := by
  have h1 : Θ ^ p ≤ Θ ^ 3 := pow_le_pow_right₀ hΘ hp
  have h0 : 0 ≤ Θ ^ 3 := pow_nonneg (zero_le_one.trans hΘ) 3
  calc 2 * Θ ^ p * X ≤ 2 * Θ ^ 3 * X := mul_le_mul_of_nonneg_right (by linarith) hX
    _ ≤ 2 * Θ ^ 3 * Y := mul_le_mul_of_nonneg_left hXY (by linarith)

/-- `2 Θ³ C_sym ≤ ĉ_step`. -/
theorem two_Theta_cube_mul_C_sym_le_hatcStep (hP : Params n τ M σK σB σT) :
    2 * Theta n M σK σB σT ^ 3 * C_sym n τ M σK σB σT ≤ hatcStep n τ M σK σB σT := by
  unfold hatcStep
  exact two_pow_mul_le_aux (one_le_Theta hP) le_rfl (zero_le_one.trans (one_le_C_sym hP))
    (le_max_left _ _)

/-- `2 Θ² Ĉ_Δ ≤ ĉ_step`. -/
theorem two_Theta_sq_mul_hatCDelta_le_hatcStep (hP : Params n τ M σK σB σT) :
    2 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT ≤ hatcStep n τ M σK σB σT := by
  have h0 := zero_le_one.trans (one_le_hatCDelta hP)
  have h1 := one_le_mSize_mul_CDTbord hP
  have hle : hatCDelta n τ M σK σB σT ≤
      mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT := by
    calc hatCDelta n τ M σK σB σT = 1 * hatCDelta n τ M σK σB σT := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 h0
  unfold hatcStep
  exact two_pow_mul_le_aux (one_le_Theta hP) (by norm_num) h0 (hle.trans (le_max_right _ _))

/-- `Θ² (2𝔪 C_{Δ𝖳} Ĉ_Δ) ≤ ĉ_step`. -/
theorem Theta_sq_mul_two_mSize_CDTbord_hatCDelta_le_hatcStep (hP : Params n τ M σK σB σT) :
    Theta n M σK σB σT ^ 2 *
        (2 * mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT) ≤
      hatcStep n τ M σK σB σT := by
  have h0 : 0 ≤ mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT :=
    mul_nonneg (zero_le_one.trans (one_le_mSize_mul_CDTbord hP))
      (zero_le_one.trans (one_le_hatCDelta hP))
  have h := two_pow_mul_le_aux (Θ := Theta n M σK σB σT) (p := 2) (one_le_Theta hP)
    (by norm_num) h0 (le_refl (mSize M σK σB σT * CDTbord n M σK σB σT *
      hatCDelta n τ M σK σB σT))
  have hmax : 2 * Theta n M σK σB σT ^ 3 *
      (mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT) ≤
      hatcStep n τ M σK σB σT := by
    unfold hatcStep
    exact mul_le_mul_of_nonneg_left (le_max_right _ _)
      (by have := zero_le_one.trans (one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT))
          positivity)
  calc _ = 2 * Theta n M σK σB σT ^ 2 *
        (mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT) := by ring
    _ ≤ _ := h.trans hmax

/-- Step `st-small`: from `ĉ_step ε/(γ⁴ δ^(2a)) ≤ min {1, β}`, `γ ≤ Θ`, `δ ≤ 1`:
`C_sym ε/(γ δ^(κ+1)) ≤ 1/2`, `d ≤ β/2` and `2𝔪 C_{Δ𝖳} d/δ² ≤ 1` for `d = Ĉ_Δ ε/(γ² δ^a)`. -/
theorem iso_step_small (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hsmall : hatcStep n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ min 1 β) :
    C_sym n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ≤ 1 / 2 ∧
    dStep n τ M σK σB σT γ ε δ ≤ β / 2 ∧
    2 * mSize M σK σB σT * CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 ≤ 1 := by
  have ha := eight_le_aExp hP
  have hQ1 : hatcStep n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ 1 :=
    hsmall.trans (min_le_left _ _)
  have hQβ : hatcStep n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ β :=
    hsmall.trans (min_le_right _ _)
  have hhalf : hatcStep n τ M σK σB σT / 2 * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) =
      hatcStep n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) / 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · have h := absorb_mul_le (i := 1) (k := 4) (j := kappa n τ + 1) (J := 2 * aExp n τ)
      (c := hatcStep n τ M σK σB σT / 2) hγ hγΘ hδ hδ1 (by norm_num)
      (by linarith [aExp_eq (n := n) (τ := τ), one_le_kappa hP]) hε
      (zero_le_one.trans (one_le_C_sym hP))
      (by have := two_Theta_cube_mul_C_sym_le_hatcStep hP; norm_num; linarith)
    rw [hhalf, pow_one] at h
    linarith
  · have h := absorb_mul_le (i := 2) (k := 4) (j := aExp n τ) (J := 2 * aExp n τ)
      (c := hatcStep n τ M σK σB σT / 2) hγ hγΘ hδ hδ1 (by norm_num) (by linarith) hε
      (zero_le_one.trans (one_le_hatCDelta hP))
      (by have := two_Theta_sq_mul_hatCDelta_le_hatcStep hP; norm_num; linarith)
    rw [hhalf] at h
    show hatCDelta n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ≤ β / 2
    linarith
  · have hrw : 2 * mSize M σK σB σT * CDTbord n M σK σB σT *
          dStep n τ M σK σB σT γ ε δ / δ ^ 2 =
        (2 * mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT) * ε /
          (γ ^ 2 * δ ^ (aExp n τ + 2)) := by
      unfold dStep
      rw [Real.rpow_add hδ, Real.rpow_two]
      have h2 : 0 < δ ^ aExp n τ := Real.rpow_pos_of_pos hδ _
      field_simp
    have hX : 0 ≤ 2 * mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT := by
      have := zero_le_one.trans (one_le_mSize_mul_CDTbord hP)
      have := zero_le_one.trans (one_le_hatCDelta hP)
      have h2 : 2 * mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT =
          2 * (mSize M σK σB σT * CDTbord n M σK σB σT) * hatCDelta n τ M σK σB σT := by ring
      rw [h2]
      positivity
    have h := absorb_mul_le (i := 2) (k := 4) (j := aExp n τ + 2) (J := 2 * aExp n τ)
      (c := hatcStep n τ M σK σB σT) hγ hγΘ hδ hδ1 (by norm_num) (by linarith) hε hX
      (by have := Theta_sq_mul_two_mSize_CDTbord_hatCDelta_le_hatcStep hP; norm_num; linarith)
    rw [hrw]
    linarith

end Step

/-! ### Steps `it-sums`, `it-stepsmall`: the induction -/

section Iteration

variable {n : ℕ} {τ M σK σB σT : ℝ} {γ d0 e μ ν : ℝ}

/-- The hypothesis of the error decay lemma from `ĉ_* e/(γ⁴ δ₀^(2a)) ≤ 1`, since
`ĉ_* ≥ 2^(2a) Ĉ_E`. -/
theorem iso_error_decay_hyp (hγ : 0 < γ) (hd0 : 0 < d0) (he : 0 ≤ e)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1 := by
  refine le_trans ?_ hsmall
  apply div_le_div_of_nonneg_right _ (mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)).le
  exact mul_le_mul_of_nonneg_right (two_rpow_mul_hatCE_le_hatcStar μ ν) he

/-- `ĉ_sum e/(γ⁴ δ₀^(2a)) ≤ μ/2` from `ĉ_* e/(γ⁴ δ₀^(2a)) ≤ 1`, since `ĉ_* ≥ 2 ĉ_sum/μ`. -/
theorem iso_c_sum_small (hγ : 0 < γ) (hd0 : 0 < d0) (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    hatcSum n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ μ / 2 := by
  have hD : 0 < γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)
  have h1 : 2 * hatcSum n τ M σK σB σT ≤ hatcStar n τ M σK σB σT μ ν * μ :=
    (div_le_iff₀ hμ).1 (two_mul_hatcSum_div_le_hatcStar μ ν)
  have h2 : hatcSum n τ M σK σB σT * e ≤ (μ / 2) * (hatcStar n τ M σK σB σT μ ν * e) := by
    have := mul_le_mul_of_nonneg_right h1 he
    nlinarith
  have h3 : hatcStar n τ M σK σB σT μ ν * e ≤ γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    (div_le_one hD).1 hsmall
  rw [div_le_iff₀ hD]
  calc hatcSum n τ M σK σB σT * e ≤ (μ / 2) * (hatcStar n τ M σK σB σT μ ν * e) := h2
    _ ≤ (μ / 2) * (γ ^ 4 * d0 ^ (2 * aExp n τ)) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)

/-- Step `it-stepsmall`: `ĉ_step e/(γ⁴ δ₀^(2a)) ≤ min {1, μ/2}`, since
`ĉ_* ≥ ĉ_step max {1, 2/μ}`. -/
theorem iso_iteration_step_small (hP : Params n τ M σK σB σT) (hγ : 0 < γ) (hd0 : 0 < d0)
    (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    hatcStep n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ min 1 (μ / 2) := by
  have hD : 0 < γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)
  have hc0 := zero_le_one.trans (one_le_hatcStep hP)
  have h3 : hatcStar n τ M σK σB σT μ ν * e ≤ γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    (div_le_one hD).1 hsmall
  have hmax := hatcStep_mul_max_le_hatcStar (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB)
    (σT := σT) μ ν
  have hA : hatcStep n τ M σK σB σT ≤ hatcStar n τ M σK σB σT μ ν :=
    le_trans (le_mul_of_one_le_right hc0 (le_max_left _ _)) hmax
  have hB : hatcStep n τ M σK σB σT * (2 / μ) ≤ hatcStar n τ M σK σB σT μ ν :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0) hmax
  refine le_min ?_ ?_
  · rw [div_le_one hD]
    exact (mul_le_mul_of_nonneg_right hA he).trans h3
  · rw [div_le_iff₀ hD]
    have h4 : hatcStep n τ M σK σB σT * (2 / μ) * e ≤ γ ^ 4 * d0 ^ (2 * aExp n τ) :=
      (mul_le_mul_of_nonneg_right hB he).trans h3
    have h5 : hatcStep n τ M σK σB σT * e = (μ / 2) * (hatcStep n τ M σK σB σT * (2 / μ) * e) := by
      field_simp
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 (by linarith)

/-- The abstract summed bound: for `X ≥ 0` with `4 Θ² X ≤ c`, an exponent `j ≤ 2a` and
`c e/(γ⁴ δ₀^(2a)) ≤ l`: `(X/γ²) · (2e/δ₀^j) ≤ l/2`. Here `2e/δ₀^j` is the bound of
`∑_s ε_s/δ_s^j` of the error decay lemma. -/
theorem sum_coef_le_gen (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT) (hd0 : 0 < d0)
    (hd01 : d0 ≤ 1) (he : 0 ≤ e) {X j c l : ℝ} (hX : 0 ≤ X)
    (hXc : 4 * Theta n M σK σB σT ^ 2 * X ≤ c) (hj : j ≤ 2 * aExp n τ)
    (hsmall : c * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ l) :
    X / γ ^ 2 * (2 * e / d0 ^ j) ≤ l / 2 := by
  have hrw : X / γ ^ 2 * (2 * e / d0 ^ j) = (2 * X) * e / (γ ^ 2 * d0 ^ j) := by
    have : d0 ^ j ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
    field_simp
  have h := absorb_mul_le (i := 2) (k := 4) (X := 2 * X) (j := j) (J := 2 * aExp n τ)
    (c := c / 2) hγ hγΘ hd0 hd01 (by norm_num) hj he (by linarith)
    (by simp only [show (4 - 2 : ℕ) = 2 from rfl]; linarith)
  have h2 : c / 2 * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) =
      c * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) / 2 := by ring
  rw [hrw]
  rw [h2] at h
  linarith

theorem four_Theta_sq_mul_hatCDelta_le_hatcSum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT ≤ hatcSum n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT :=
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_hatCDelta hP))
  unfold hatcSum
  calc 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT
      = 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hn.trans (le_max_left _ _)) h0

theorem four_Theta_sq_mul_n_mul_hatCDelta_le_hatcSum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 * ((n : ℝ) * hatCDelta n τ M σK σB σT) ≤
      hatcSum n τ M σK σB σT := by
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT :=
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_hatCDelta hP))
  unfold hatcSum
  calc 4 * Theta n M σK σB σT ^ 2 * ((n : ℝ) * hatCDelta n τ M σK σB σT)
      = 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT * n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) h0

theorem four_Theta_sq_mul_C_B_mul_hatCDelta_le_hatcSum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 * (C_B n M σK σB σT * hatCDelta n τ M σK σB σT) ≤
      hatcSum n τ M σK σB σT := by
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT :=
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_hatCDelta hP))
  unfold hatcSum
  calc 4 * Theta n M σK σB σT ^ 2 * (C_B n M σK σB σT * hatCDelta n τ M σK σB σT)
      = 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT * C_B n M σK σB σT := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) h0

theorem four_Theta_sq_mul_mSize_sq_CDTbord_hatCDelta_le_hatcSum
    (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 *
      (mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT) ≤
        hatcSum n τ M σK σB σT := by
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT :=
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_hatCDelta hP))
  unfold hatcSum
  calc 4 * Theta n M σK σB σT ^ 2 *
        (mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT)
      = 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT *
          (mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_right _ _)) h0

/-- Step `it-sums`: the summed bounds, in the form `coefficient/γ² · (2e/δ₀^j) ≤ …` for
`j = a, a, a+1, a+1, a+2`, namely the bounds for `∑ d_s ≤ μ/4`, `∑ d_s ≤ ν/2`,
`∑ n d_s/δ_s ≤ μ/4`, `∑ C_B d_s/δ_s ≤ μ/4` and `∑ 2𝔪² C_{Δ𝖳} d_s/δ_s² ≤ μ/2`. -/
theorem iso_iteration_sums (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hd0 : 0 < d0) (hd01 : d0 ≤ 1) (he : 0 ≤ e) (hμ : 0 < μ)
    (hν : 0 < ν)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ aExp n τ) ≤ μ / 4 ∧
    hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ aExp n τ) ≤ ν / 2 ∧
    (n : ℝ) * hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ (aExp n τ + 1)) ≤ μ / 4 ∧
    C_B n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
      (2 * e / d0 ^ (aExp n τ + 1)) ≤ μ / 4 ∧
    2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
      (2 * e / d0 ^ (aExp n τ + 2)) ≤ μ / 2 := by
  have ha := eight_le_aExp hP
  have hn := zero_le_one.trans hP.one_le_cast
  have hcs : hatcSum n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ μ / 2 :=
    iso_c_sum_small hγ hd0 he hμ hsmall
  have hΔ0 := zero_le_one.trans (one_le_hatCDelta hP)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := sum_coef_le_gen hγ hγΘ hd0 hd01 he hΔ0 (four_Theta_sq_mul_hatCDelta_le_hatcSum hP)
      (j := aExp n τ) (by linarith) hcs
    linarith
  · have hXc : 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT ≤
        ν * hatcStar n τ M σK σB σT μ ν := by
      have := (div_le_iff₀ hν).1 (four_Theta_sq_mul_hatCDelta_div_le_hatcStar (n := n) (τ := τ)
        (M := M) (σK := σK) (σB := σB) (σT := σT) μ ν)
      linarith
    have hs : ν * hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ ν := by
      have e1 : ν * hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) =
          ν * (hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ))) := by ring
      rw [e1]
      nlinarith
    exact sum_coef_le_gen hγ hγΘ hd0 hd01 he hΔ0 hXc (j := aExp n τ) (by linarith) hs
  · have := sum_coef_le_gen hγ hγΘ hd0 hd01 he (X := (n : ℝ) * hatCDelta n τ M σK σB σT)
      (mul_nonneg hn hΔ0) (four_Theta_sq_mul_n_mul_hatCDelta_le_hatcSum hP)
      (j := aExp n τ + 1) (by linarith) hcs
    linarith
  · have := sum_coef_le_gen hγ hγΘ hd0 hd01 he (X := C_B n M σK σB σT * hatCDelta n τ M σK σB σT)
      (mul_nonneg (zero_le_one.trans (one_le_C_B hP)) hΔ0)
      (four_Theta_sq_mul_C_B_mul_hatCDelta_le_hatcSum hP) (j := aExp n τ + 1) (by linarith) hcs
    linarith
  · have hY : 0 ≤ mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT := by
      have := zero_le_one.trans (one_le_CDTbord hP)
      have := zero_le_one.trans (one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT))
      positivity
    have h := sum_coef_le_gen hγ hγΘ hd0 hd01 he
      (X := mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT)
      hY (four_Theta_sq_mul_mSize_sq_CDTbord_hatCDelta_le_hatcSum hP) (j := aExp n τ + 2)
      (by linarith) hcs
    have heq : 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT /
          γ ^ 2 * (2 * e / d0 ^ (aExp n τ + 2)) =
        2 * (mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
          (2 * e / d0 ^ (aExp n τ + 2))) := by ring
    rw [heq]
    linarith

/-- The closeness bounds of the limit: `2 Ĉ_Δ e/(γ² δ₀^a) ≤ μ/4` and `≤ ν/2`. -/
theorem iso_closeness_le (hP : Params n τ M σK σB σT) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hd0 : 0 < d0) (hd01 : d0 ≤ 1) (he : 0 ≤ e) (hμ : 0 < μ)
    (hν : 0 < ν)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * d0 ^ aExp n τ) ≤ μ / 4 ∧
    2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * d0 ^ aExp n τ) ≤ ν / 2 := by
  have h := iso_iteration_sums hP hγ hγΘ hd0 hd01 he hμ hν hsmall
  have hd : d0 ^ aExp n τ ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
  have heq : hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ aExp n τ) =
      2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * d0 ^ aExp n τ) := by
    field_simp
  rw [← heq]
  exact ⟨h.1, h.2.1⟩

end Iteration

/-! ### Steps `g1-e`, `g1-o`: the constants of I-G1 -/

section G1

variable {n : ℕ} {τ M σK σB σT : ℝ}

/-- Step `g1-constants`: `C₁ > 0`. -/
theorem isoC1_pos {ρ ρinf μ ν γbar : ℝ} (hρ : 0 < ρ) (hγbar : 0 < γbar) :
    0 < isoC1 n τ ρ ρinf M σK σB σT μ ν γbar :=
  mul_pos (Real.rpow_pos_of_pos hρ _) (lt_max_of_lt_left (pow_pos hγbar 4))

/-- Step `g1-constants`: `C₂ > 0`. -/
theorem isoC2_pos {ρ ρinf : ℝ} (hP : Params n τ M σK σB σT) (hρ : 0 < ρ) (hρinf : ρinf < ρ) :
    0 < isoC2 n τ ρ ρinf M σK σB σT :=
  mul_pos (mul_pos (mul_pos two_pos (zero_lt_one.trans_le (one_le_hatCDelta hP)))
    (Real.rpow_pos_of_pos hρ _)) (Real.rpow_pos_of_pos (delta0_pos hρinf) _)

/-- Step `g1-e`: the hypothesis `C₁ e/(γ⁴ ρ^(4τ)) < 1` of I-G1 gives `e < 1` and
`ĉ_* e/(γ⁴ δ₀^(2a)) < 1`, where `C₁ = ρ^(4τ) max {γ̄⁴, ĉ_* δ₀^(-2a)}`. -/
theorem iso_g1_error_small (hP : Params n τ M σK σB σT) {ρ ρinf γ γbar μ ν e : ℝ}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (h : isoC1 n τ ρ ρinf M σK σB σT μ ν γbar * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1) :
    e < 1 ∧ hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) < 1 :=
  g1_error_small_aux (hρinf.trans hρ) hγ hγγbar (delta0_pos hρ)
    (zero_le_one.trans (one_le_hatcStar hP μ ν)) h

/-- Step `g1-o`: `2 Ĉ_Δ e/(γ² δ₀^a) = C₂ e/(γ² ρ^(2τ))`, `C₂ = 2 Ĉ_Δ ρ^(2τ) δ₀^(-a)`. -/
theorem iso_g1_closeness_eq {ρ ρinf γ e : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hρinf : ρinf < ρ) :
    2 * hatCDelta n τ M σK σB σT * e / (γ ^ 2 * delta0 ρ ρinf ^ aExp n τ) =
      isoC2 n τ ρ ρinf M σK σB σT * e / (γ ^ 2 * ρ ^ (2 * τ)) :=
  g1_closeness_eq hρ hγ (delta0_pos hρinf)

end G1

end KAM.Iso.Apost.Arith
