/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Constants of Part 2 (isoenergetic): the claims of `bpI:p2:constants`

The definitions of the constants (`hatCS`, ..., `hatcStar`, `dStep`) are in
`KAM/Iso/Apost/Defs.lean`; each takes exactly the parameters it depends on, so every
"depends only on" claim of the blueprint is syntactic. This module proves the claims of Definition
`bpI:p2:constants`: the constants are `≥ 1`, `C_ΔT ≤ C_{Δ𝖳}`, `κ ≥ 3` and `a ≥ 8`
(`iso_constants_spec`), together with the elementary orderings between the constants that the
arithmetic of `KAM/Iso/Apost/ConstantsArith.lean` uses.

The constants of `KAM.Apost` (`kappa`, `aExp`, `cR`, `mSize`, `Theta`, `C_X`, `C_T`, `C_Omega`,
`C_sym`, `C_red`, `C_xi0`, `C_G`, `C_B`, `C_DN`, `C_DX`, `C_DT`, `delta0`) and their facts
(`one_le_C_*`, `one_le_Theta`, `eight_le_aExp`, ...) are reused unchanged.
-/

public section

namespace KAM.Iso.Apost

open KAM.Apost

variable {n : ℕ} {τ M σK σB σT : ℝ}

/-! ### `κ ≥ 3` -/

theorem three_le_kappa (hP : Params n τ M σK σB σT) : 3 ≤ kappa n τ := by
  have h2 := hP.two_le_cast
  have h1 := hP.tau_ge
  unfold kappa
  linarith

/-! ### The constants are `≥ 1` -/

theorem one_le_hatCS (hP : Params n τ M σK σB σT) : 1 ≤ hatCS n τ M σK σB σT :=
  (one_le_C_xi0 hP).trans (le_max_left _ _)

theorem one_le_hatCxiN (hP : Params n τ M σK σB σT) : 1 ≤ hatCxiN n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have h1 := one_le_hatCS hP
  have h2 : 0 ≤ 2 * (n : ℝ) * cR n τ * mSize M σK σB σT :=
    mul_nonneg (mul_nonneg (by linarith) (zero_le_one.trans one_le_cR))
      (zero_le_one.trans one_le_mSize)
  unfold hatCxiN
  linarith

theorem one_le_hatCg (hP : Params n τ M σK σB σT) : 1 ≤ hatCg n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have hΘ := one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT)
  have h1 : 1 ≤ C_T n M σK σB σT * hatCxiN n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_C_T hP) (one_le_hatCxiN hP)
  have h2 : 0 ≤ Theta n M σK σB σT * hatCS n τ M σK σB σT :=
    mul_nonneg (zero_le_one.trans hΘ) (zero_le_one.trans (one_le_hatCS hP))
  have h3 : 0 ≤ 2 * (n : ℝ) * mSize M σK σB σT ^ 2 * Theta n M σK σB σT :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (zero_le_one.trans hΘ)
  unfold hatCg
  linarith

theorem one_le_hatCxi (hP : Params n τ M σK σB σT) : 1 ≤ hatCxi n τ M σK σB σT :=
  (one_le_mul_of_one_le_of_one_le one_le_cR (one_le_hatCg hP)).trans (le_max_left _ _)

theorem one_le_hatCDK (hP : Params n τ M σK σB σT) : 1 ≤ hatCDK n τ M σK σB σT := by
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  unfold hatCDK
  exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_hatCxi hP)

theorem one_le_hatCDelta (hP : Params n τ M σK σB σT) : 1 ≤ hatCDelta n τ M σK σB σT :=
  (one_le_hatCDK hP).trans (le_max_left _ _)

theorem one_le_CP (hP : Params n τ M σK σB σT) : 1 ≤ CP n M σK σB σT := by
  have hn := hP.one_le_cast
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have h2 : 0 ≤ mSize M σK σB σT ^ 2 := sq_nonneg _
  have h3 : 0 ≤ mSize M σK σB σT ^ 3 := pow_nonneg (by linarith) 3
  have hX := one_le_C_X hP
  unfold CP
  linarith

theorem one_le_hatCpartial (hP : Params n τ M σK σB σT) : 1 ≤ hatCpartial n τ M σK σB σT := by
  have hΘ := one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT)
  have h1 : 1 ≤ CP n M σK σB σT * hatCxi n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_CP hP) (one_le_hatCxi hP)
  have h2 : 0 ≤ 2 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT * hatCg n τ M σK σB σT :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (zero_le_one.trans hΘ))
      (zero_le_one.trans (one_le_hatCg hP))
  unfold hatCpartial
  linarith

theorem one_le_hatClin (hP : Params n τ M σK σB σT) : 1 ≤ hatClin n τ M σK σB σT := by
  have hΘ := one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT)
  have h1 : 1 ≤ C_red n M σK σB σT * hatCxi n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_C_red hP) (one_le_hatCxi hP)
  have h2 : 0 ≤ C_sym n τ M σK σB σT * hatCg n τ M σK σB σT :=
    mul_nonneg (zero_le_one.trans (one_le_C_sym hP)) (zero_le_one.trans (one_le_hatCg hP))
  have h3 : 0 ≤ Theta n M σK σB σT * C_Omega n τ M σK σB σT * hatCS n τ M σK σB σT :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hΘ) (zero_le_one.trans (one_le_C_Omega hP)))
      (zero_le_one.trans (one_le_hatCS hP))
  unfold hatClin
  linarith

theorem one_le_hatCE1 (hP : Params n τ M σK σB σT) : 1 ≤ hatCE1 n τ M σK σB σT := by
  have hΘ := one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have h4 : 1 ≤ 4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hm)) (one_le_pow₀ hΘ)
  have h1 : 1 ≤ 4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 * hatClin n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le h4 (one_le_hatClin hP)
  have h2 : 0 ≤ mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2 :=
    mul_nonneg (zero_le_one.trans hm) (sq_nonneg _)
  have h3 : 0 ≤ Theta n M σK σB σT * hatCS n τ M σK σB σT * hatCpartial n τ M σK σB σT :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hΘ) (zero_le_one.trans (one_le_hatCS hP)))
      (zero_le_one.trans (one_le_hatCpartial hP))
  unfold hatCE1
  linarith

theorem one_le_hatCE2 (hP : Params n τ M σK σB σT) : 1 ≤ hatCE2 n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have hΘ := one_le_Theta hP (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have hΩ : 1 ≤ 2 * (n : ℝ) * mSize M σK σB σT + C_Omega n τ M σK σB σT := by
    have := one_le_C_Omega hP (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB) (σT := σT)
    have : 0 ≤ 2 * (n : ℝ) * mSize M σK σB σT := by positivity
    linarith
  have h1 : 1 ≤ n * Theta n M σK σB σT ^ 2 *
      (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT) * cR n τ * hatCg n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hn (one_le_pow₀ hΘ)) hΩ) one_le_cR)
      (one_le_hatCg hP)
  have h2 : 0 ≤ mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2 :=
    mul_nonneg (zero_le_one.trans hm) (sq_nonneg _)
  unfold hatCE2
  linarith

theorem one_le_hatCE (hP : Params n τ M σK σB σT) : 1 ≤ hatCE n τ M σK σB σT :=
  (one_le_hatCE1 hP).trans (le_max_left _ _)

theorem one_le_CY (hP : Params n τ M σK σB σT) : 1 ≤ CY n M σK σB σT := by
  have hn := hP.one_le_cast
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have h1 : 1 ≤ 2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT := by
    have := one_le_C_DN hP (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB) (σT := σT)
    have : 0 ≤ mSize M σK σB σT ^ 2 := sq_nonneg _
    linarith
  unfold CY
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hm) h1

/-- `C_ΔT ≤ C_{Δ𝖳}`. -/
theorem C_DT_le_CDTbord (hP : Params n τ M σK σB σT) :
    C_DT n M σK σB σT ≤ CDTbord n M σK σB σT := by
  have hn := hP.one_le_cast
  have h1 : 0 ≤ 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 := by positivity
  have h2 := one_le_CY hP (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB) (σT := σT)
  unfold CDTbord
  linarith

theorem one_le_CDTbord (hP : Params n τ M σK σB σT) : 1 ≤ CDTbord n M σK σB σT :=
  (one_le_C_DT hP).trans (C_DT_le_CDTbord hP)

theorem one_le_mSize_mul_CDTbord (hP : Params n τ M σK σB σT) :
    1 ≤ mSize M σK σB σT * CDTbord n M σK σB σT :=
  one_le_mul_of_one_le_of_one_le one_le_mSize (one_le_CDTbord hP)

theorem one_le_hatcStep (hP : Params n τ M σK σB σT) : 1 ≤ hatcStep n τ M σK σB σT := by
  have hΘ3 : 1 ≤ Theta n M σK σB σT ^ 3 := one_le_pow₀ (one_le_Theta hP)
  have hmax : 1 ≤ max (C_sym n τ M σK σB σT)
      (mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT) :=
    (one_le_C_sym hP).trans (le_max_left _ _)
  unfold hatcStep
  exact one_le_mul_of_one_le_of_one_le (by linarith) hmax

theorem one_le_hatcSum (hP : Params n τ M σK σB σT) : 1 ≤ hatcSum n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have hΘ2 : 1 ≤ Theta n M σK σB σT ^ 2 := one_le_pow₀ (one_le_Theta hP)
  have hmax : 1 ≤ max (n : ℝ) (max (C_B n M σK σB σT)
      (mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT)) := hn.trans (le_max_left _ _)
  unfold hatcSum
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_hatCDelta hP)) hmax

theorem one_le_hatcStar (hP : Params n τ M σK σB σT) (μ ν : ℝ) :
    1 ≤ hatcStar n τ M σK σB σT μ ν := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * aExp n τ) :=
    Real.one_le_rpow (by norm_num) (by linarith [four_le_aExp hP])
  unfold hatcStar
  exact (one_le_mul_of_one_le_of_one_le h1 (one_le_hatCE hP)).trans (le_max_left _ _)

/-! ### Orderings between the constants -/

theorem hatCDK_le_hatCDelta : hatCDK n τ M σK σB σT ≤ hatCDelta n τ M σK σB σT :=
  le_max_left _ _

theorem Theta_sq_mul_hatCS_le_hatCDelta :
    Theta n M σK σB σT ^ 2 * hatCS n τ M σK σB σT ≤ hatCDelta n τ M σK σB σT :=
  le_max_right _ _

theorem C_xi0_le_hatCS : C_xi0 n τ M σK σB σT ≤ hatCS n τ M σK σB σT := le_max_left _ _

theorem mSize_mul_Theta_add_le_hatCS :
    mSize M σK σB σT * Theta n M σK σB σT + 2 * n * cR n τ * mSize M σK σB σT ^ 5 ≤
      hatCS n τ M σK σB σT :=
  le_max_right _ _

theorem cR_mul_hatCg_le_hatCxi :
    cR n τ * hatCg n τ M σK σB σT ≤ hatCxi n τ M σK σB σT := le_max_left _ _

theorem Theta_mul_hatCxiN_le_hatCxi :
    Theta n M σK σB σT * hatCxiN n τ M σK σB σT ≤ hatCxi n τ M σK σB σT := le_max_right _ _

theorem hatCE1_le_hatCE : hatCE1 n τ M σK σB σT ≤ hatCE n τ M σK σB σT := le_max_left _ _

theorem hatCE2_le_hatCE : hatCE2 n τ M σK σB σT ≤ hatCE n τ M σK σB σT := le_max_right _ _

theorem two_rpow_mul_hatCE_le_hatcStar (μ ν : ℝ) :
    (2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT ≤ hatcStar n τ M σK σB σT μ ν :=
  le_max_left _ _

theorem hatcStep_mul_max_le_hatcStar (μ ν : ℝ) :
    hatcStep n τ M σK σB σT * max 1 (2 / μ) ≤ hatcStar n τ M σK σB σT μ ν :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem two_mul_hatcSum_div_le_hatcStar (μ ν : ℝ) :
    2 * hatcSum n τ M σK σB σT / μ ≤ hatcStar n τ M σK σB σT μ ν :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem four_Theta_sq_mul_hatCDelta_div_le_hatcStar (μ ν : ℝ) :
    4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT / ν ≤ hatcStar n τ M σK σB σT μ ν :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- `bpI:p2:constants`, the claims: positivity (`≥ 1`), `κ ≥ 3`, `a ≥ 8`, `C_ΔT ≤ C_{Δ𝖳}`. -/
theorem iso_constants_spec {τ M σK σB σT : ℝ} (hP : Params n τ M σK σB σT) (μ ν : ℝ) :
    1 ≤ hatCS n τ M σK σB σT ∧ 1 ≤ hatCxiN n τ M σK σB σT ∧ 1 ≤ hatCg n τ M σK σB σT ∧
    1 ≤ hatCxi n τ M σK σB σT ∧ 1 ≤ hatCDK n τ M σK σB σT ∧ 1 ≤ hatCDelta n τ M σK σB σT ∧
    1 ≤ CP n M σK σB σT ∧ 1 ≤ hatCpartial n τ M σK σB σT ∧ 1 ≤ hatClin n τ M σK σB σT ∧
    1 ≤ hatCE n τ M σK σB σT ∧ 1 ≤ CY n M σK σB σT ∧ C_DT n M σK σB σT ≤ CDTbord n M σK σB σT ∧
    1 ≤ hatcStep n τ M σK σB σT ∧ 1 ≤ hatcSum n τ M σK σB σT ∧
    1 ≤ hatcStar n τ M σK σB σT μ ν ∧ 3 ≤ kappa n τ ∧ 8 ≤ aExp n τ :=
  ⟨one_le_hatCS hP, one_le_hatCxiN hP, one_le_hatCg hP, one_le_hatCxi hP, one_le_hatCDK hP,
    one_le_hatCDelta hP, one_le_CP hP, one_le_hatCpartial hP, one_le_hatClin hP, one_le_hatCE hP,
    one_le_CY hP, C_DT_le_CDTbord hP, one_le_hatcStep hP, one_le_hatcSum hP,
    one_le_hatcStar hP μ ν, three_le_kappa hP, eight_le_aExp hP⟩

end KAM.Iso.Apost
