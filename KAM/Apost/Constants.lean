/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Standing
public import KAM.Strip.CohomologicalDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Exponents and constants of Part 2 (blueprint `bp:p2:constants`)

Each constant is a `def` taking exactly the parameters it depends on, so every "depends only on …"
claim of the blueprint is syntactic.

* `(n τ)`: `kappa` (`κ`), `aExp` (`a`), `cR` (`c_R`);
* `(M σK σB σT)`: `mSize` (`𝔪`);
* `(n M σK σB σT)`: `Theta` (`Θ`), `C_X`, `C_T`, `C_red`, `C_G`, `C_B`, `C_DN`, `C_DX`, `C_DT`;
* `(n τ M σK σB σT)`: `C_Omega`, `C_sym`, `C_xi0`, `C_xiN`, `C_g`, `C_xi`, `C_DK`, `C_lin`, `C_E`,
  `c_step`, `c_sum`;
* `(n τ M σK σB σT μ)`: `c_star` (`𝔠_*`);
* `(ρ ρinf)`: `delta0` (`δ₀`).

`KAM.Apost.constants_spec` records the claims of the blueprint: the constants are `≥ 1`, `κ ≥ 1`,
`a ≥ 4` and `δ₀ ∈ (0, 1]`.

## The constant inequalities, proved once

Every inequality between the constants that later parts of Part 2 use is proved here, so that no
later module unfolds a constant. They are grouped by the blueprint step that uses them:

* orderings and smallness of the perturbation (`pt-small`, `pt-gram`, `pt-xn`):
  `C_DT ≥ max {n, C_G, C_DN}` (`n_le_C_DT`, `C_G_le_C_DT`, `C_DN_le_C_DT`), `gram_coeff_le`,
  `perturbation_small`, `pt_xn_sum_le`;
* absorption of powers of `γ` and `δ` (`cor-absorb`, `st-small`, `ne-total`): `mul_rpow_le`,
  `div_absorb`, `absorb_mul_le`;
* smallness of the step (`st-small`): `step_small`, from the dominance facts
  `two_Theta_pow_three_mul_C_sym_le_c_step`, `two_Theta_sq_mul_C_DK_le_c_step` and
  `four_Theta_sq_mul_le_c_step`;
* the induction (`it-sums`, `it-stepsmall`): `error_decay_hyp`, `c_sum_small`,
  `iteration_step_small`, `sum_coef_le`, `iteration_sums`, `closeness_le`;
* Theorem G1 (`g1-e`, `g1-check`): `g1_error_small`, `g1_closeness_eq`.

The hypothesis `γ ≤ Θ` of the absorption lemmas is the conclusion of Lemma `bp:p2:frequency`; the
lemmas here are arithmetic and take it as a hypothesis.
-/

@[expose] public noncomputable section

namespace KAM.Apost

variable (n : ℕ) (τ M σK σB σT : ℝ)

/-- `κ = τ + n`. -/
def kappa : ℝ := τ + n
/-- `a = 2κ + 2`. -/
def aExp : ℝ := 2 * kappa n τ + 2
/-- `c_R = max {1, c(n, τ)}`, with `c(n, τ) = KAM.cohConst n τ`. -/
def cR : ℝ := max 1 (cohConst n τ)
/-- `𝔪 = max {1, M, σ_K, σ_B, σ_T}`. -/
def mSize : ℝ := max 1 (max M (max σK (max σB σT)))
/-- `Θ = 4 n 𝔪³`. -/
def Theta : ℝ := 4 * n * mSize M σK σB σT ^ 3
/-- `C_X = 5 n² 𝔪⁵`. -/
def C_X : ℝ := 5 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 5
/-- `C_T = 2 n 𝔪² C_X`. -/
def C_T : ℝ := 2 * n * mSize M σK σB σT ^ 2 * C_X n M σK σB σT
/-- `C_Ω = 2 n (n + 1) c_R 𝔪`. -/
def C_Omega : ℝ := 2 * n * (n + 1) * cR n τ * mSize M σK σB σT
/-- `C_sym = 𝔪² C_Ω`. -/
def C_sym : ℝ := mSize M σK σB σT ^ 2 * C_Omega n τ M σK σB σT
/-- `C_red = 2 n (n + 1) 𝔪²`. -/
def C_red : ℝ := 2 * n * (n + 1) * mSize M σK σB σT ^ 2
/-- `C_{ξ₀} = 2 n 𝔪² (𝔪 Θ + c_R C_T)`. -/
def C_xi0 : ℝ := 2 * n * mSize M σK σB σT ^ 2 *
  (mSize M σK σB σT * Theta n M σK σB σT + cR n τ * C_T n M σK σB σT)
/-- `C_{ξN} = C_{ξ₀} + 2 n c_R 𝔪`. -/
def C_xiN : ℝ := C_xi0 n τ M σK σB σT + 2 * n * cR n τ * mSize M σK σB σT
/-- `C_g = C_T C_{ξN} + 2 n 𝔪² Θ`. -/
def C_g : ℝ := C_T n M σK σB σT * C_xiN n τ M σK σB σT +
  2 * n * mSize M σK σB σT ^ 2 * Theta n M σK σB σT
/-- `C_ξ = c_R C_g + Θ C_{ξN}`. -/
def C_xi : ℝ := cR n τ * C_g n τ M σK σB σT + Theta n M σK σB σT * C_xiN n τ M σK σB σT
/-- `C_ΔK = 2 𝔪² C_ξ`. -/
def C_DK : ℝ := 2 * mSize M σK σB σT ^ 2 * C_xi n τ M σK σB σT
/-- `C_lin = C_red C_ξ + C_sym C_g`. -/
def C_lin : ℝ := C_red n M σK σB σT * C_xi n τ M σK σB σT +
  C_sym n τ M σK σB σT * C_g n τ M σK σB σT
/-- `C_E = 4 𝔪² Θ² C_lin + 𝔪 C_ΔK²`. -/
def C_E : ℝ := 4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 * C_lin n τ M σK σB σT +
  mSize M σK σB σT * C_DK n τ M σK σB σT ^ 2
/-- `C_G = 6 n² 𝔪`. -/
def C_G : ℝ := 6 * (n : ℝ) ^ 2 * mSize M σK σB σT
/-- `C_B = 2 𝔪² C_G`. -/
def C_B : ℝ := 2 * mSize M σK σB σT ^ 2 * C_G n M σK σB σT
/-- `C_ΔN = 2 n 𝔪 + 𝔪 C_B`. -/
def C_DN : ℝ := 2 * n * mSize M σK σB σT + mSize M σK σB σT * C_B n M σK σB σT
/-- `C_ΔX = 2 𝔪³ + (𝔪 + n Θ) C_ΔN`. -/
def C_DX : ℝ := 2 * mSize M σK σB σT ^ 3 +
  (mSize M σK σB σT + n * Theta n M σK σB σT) * C_DN n M σK σB σT
/-- `C_ΔT = 4 n 𝔪² C_ΔX + 2 n C_ΔN C_X`. -/
def C_DT : ℝ := 4 * n * mSize M σK σB σT ^ 2 * C_DX n M σK σB σT +
  2 * n * C_DN n M σK σB σT * C_X n M σK σB σT
/-- `𝔠_step = 2 Θ⁴ max {C_sym, 2 𝔪 C_ΔT C_ΔK}`. -/
def c_step : ℝ := 2 * Theta n M σK σB σT ^ 4 * max (C_sym n τ M σK σB σT)
  (2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT)
/-- `𝔠_sum = 4 Θ² C_ΔK max {n, C_B, 𝔪² C_ΔT}`. -/
def c_sum : ℝ := 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT *
  max (n : ℝ) (max (C_B n M σK σB σT) (mSize M σK σB σT ^ 2 * C_DT n M σK σB σT))
/-- `𝔠_* = max {2^{2a} C_E, 𝔠_step max {1, 2/μ}, 2 𝔠_sum/μ}`. -/
def c_star (μ : ℝ) : ℝ := max ((2 : ℝ) ^ (2 * aExp n τ) * C_E n τ M σK σB σT)
  (max (c_step n τ M σK σB σT * max 1 (2 / μ)) (2 * c_sum n τ M σK σB σT / μ))
/-- `δ₀ = min {1, (ρ - ρ_∞)/8}`. -/
def delta0 (ρ ρinf : ℝ) : ℝ := min 1 ((ρ - ρinf) / 8)

variable {n τ M σK σB σT}

/-! ### Elementary facts about the parameters -/

theorem Params.one_le_cast (hP : Params n τ M σK σB σT) : (1 : ℝ) ≤ n := by
  have h : 1 ≤ n := by have := hP.two_le; omega
  exact_mod_cast h

theorem Params.two_le_cast (hP : Params n τ M σK σB σT) : (2 : ℝ) ≤ n := by
  exact_mod_cast hP.two_le

theorem one_le_mSize : 1 ≤ mSize M σK σB σT := le_max_left _ _

theorem M_le_mSize : M ≤ mSize M σK σB σT := (le_max_left _ _).trans (le_max_right _ _)

theorem σK_le_mSize : σK ≤ mSize M σK σB σT :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem σB_le_mSize : σB ≤ mSize M σK σB σT :=
  (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem σT_le_mSize : σT ≤ mSize M σK σB σT :=
  (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem one_le_cR : 1 ≤ cR n τ := le_max_left _ _

theorem cohConst_le_cR : cohConst n τ ≤ cR n τ := le_max_right _ _

theorem one_le_kappa (hP : Params n τ M σK σB σT) : 1 ≤ kappa n τ := by
  have := hP.two_le_cast
  have := hP.tau_ge
  unfold kappa
  linarith

theorem aExp_eq : aExp n τ = 2 * kappa n τ + 2 := rfl

theorem eight_le_aExp (hP : Params n τ M σK σB σT) : 8 ≤ aExp n τ := by
  have := hP.two_le_cast
  have := hP.tau_ge
  unfold aExp kappa
  linarith

theorem four_le_aExp (hP : Params n τ M σK σB σT) : 4 ≤ aExp n τ := by
  have := eight_le_aExp hP
  linarith

theorem one_le_Theta (hP : Params n τ M σK σB σT) : 1 ≤ Theta n M σK σB σT := by
  have hn := hP.one_le_cast
  have h3 : 1 ≤ mSize M σK σB σT ^ 3 := one_le_pow₀ one_le_mSize
  unfold Theta
  exact one_le_mul_of_one_le_of_one_le (by linarith) h3

/-! ### The constants are `≥ 1` -/

theorem one_le_C_X (hP : Params n τ M σK σB σT) : 1 ≤ C_X n M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn
  have h5 : 1 ≤ mSize M σK σB σT ^ 5 := one_le_pow₀ one_le_mSize
  unfold C_X
  exact one_le_mul_of_one_le_of_one_le (by linarith) h5

theorem one_le_C_T (hP : Params n τ M σK σB σT) : 1 ≤ C_T n M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  unfold C_T
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) h2) (one_le_C_X hP)

theorem one_le_C_Omega (hP : Params n τ M σK σB σT) : 1 ≤ C_Omega n τ M σK σB σT := by
  have hn := hP.one_le_cast
  unfold C_Omega
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) one_le_cR) one_le_mSize

theorem one_le_C_sym (hP : Params n τ M σK σB σT) : 1 ≤ C_sym n τ M σK σB σT := by
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  unfold C_sym
  exact one_le_mul_of_one_le_of_one_le h2 (one_le_C_Omega hP)

theorem one_le_C_red (hP : Params n τ M σK σB σT) : 1 ≤ C_red n M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  unfold C_red
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) h2

theorem one_le_C_xi0 (hP : Params n τ M σK σB σT) : 1 ≤ C_xi0 n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  have h1 : 1 ≤ mSize M σK σB σT * Theta n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le one_le_mSize (one_le_Theta hP)
  have h3 : 1 ≤ cR n τ * C_T n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le one_le_cR (one_le_C_T hP)
  unfold C_xi0
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) h2) (by linarith)

theorem one_le_C_xiN (hP : Params n τ M σK σB σT) : 1 ≤ C_xiN n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have h1 : 1 ≤ 2 * (n : ℝ) * cR n τ * mSize M σK σB σT :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) one_le_cR) one_le_mSize
  have h0 := one_le_C_xi0 hP
  unfold C_xiN
  linarith

theorem one_le_C_g (hP : Params n τ M σK σB σT) : 1 ≤ C_g n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  have h1 : 1 ≤ C_T n M σK σB σT * C_xiN n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_C_T hP) (one_le_C_xiN hP)
  have h3 : 1 ≤ 2 * (n : ℝ) * mSize M σK σB σT ^ 2 * Theta n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) h2) (one_le_Theta hP)
  unfold C_g
  linarith

theorem one_le_C_xi (hP : Params n τ M σK σB σT) : 1 ≤ C_xi n τ M σK σB σT := by
  have h1 : 1 ≤ cR n τ * C_g n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le one_le_cR (one_le_C_g hP)
  have h3 : 1 ≤ Theta n M σK σB σT * C_xiN n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_Theta hP) (one_le_C_xiN hP)
  unfold C_xi
  linarith

theorem one_le_C_DK (hP : Params n τ M σK σB σT) : 1 ≤ C_DK n τ M σK σB σT := by
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  unfold C_DK
  exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_C_xi hP)

theorem one_le_C_lin (hP : Params n τ M σK σB σT) : 1 ≤ C_lin n τ M σK σB σT := by
  have h1 : 1 ≤ C_red n M σK σB σT * C_xi n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_C_red hP) (one_le_C_xi hP)
  have h3 : 1 ≤ C_sym n τ M σK σB σT * C_g n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (one_le_C_sym hP) (one_le_C_g hP)
  unfold C_lin
  linarith

theorem one_le_C_E (hP : Params n τ M σK σB σT) : 1 ≤ C_E n τ M σK σB σT := by
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  have hΘ : 1 ≤ Theta n M σK σB σT ^ 2 := one_le_pow₀ (one_le_Theta hP)
  have hK : 1 ≤ C_DK n τ M σK σB σT ^ 2 := one_le_pow₀ (one_le_C_DK hP)
  have h1 : 1 ≤ 4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 *
      C_lin n τ M σK σB σT :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) hΘ) (one_le_C_lin hP)
  have h3 : 1 ≤ mSize M σK σB σT * C_DK n τ M σK σB σT ^ 2 :=
    one_le_mul_of_one_le_of_one_le one_le_mSize hK
  unfold C_E
  linarith

theorem one_le_C_G (hP : Params n τ M σK σB σT) : 1 ≤ C_G n M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn
  unfold C_G
  exact one_le_mul_of_one_le_of_one_le (by linarith) one_le_mSize

theorem one_le_C_B (hP : Params n τ M σK σB σT) : 1 ≤ C_B n M σK σB σT := by
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  unfold C_B
  exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_C_G hP)

theorem one_le_C_DN (hP : Params n τ M σK σB σT) : 1 ≤ C_DN n M σK σB σT := by
  have hn := hP.one_le_cast
  have h1 : 1 ≤ 2 * (n : ℝ) * mSize M σK σB σT :=
    one_le_mul_of_one_le_of_one_le (by linarith) one_le_mSize
  have h3 : 1 ≤ mSize M σK σB σT * C_B n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le one_le_mSize (one_le_C_B hP)
  unfold C_DN
  linarith

theorem one_le_C_DX (hP : Params n τ M σK σB σT) : 1 ≤ C_DX n M σK σB σT := by
  have hn := hP.one_le_cast
  have h3 : 1 ≤ mSize M σK σB σT ^ 3 := one_le_pow₀ one_le_mSize
  have h1 : 1 ≤ mSize M σK σB σT + n * Theta n M σK σB σT := by
    have : 1 ≤ (n : ℝ) * Theta n M σK σB σT :=
      one_le_mul_of_one_le_of_one_le hn (one_le_Theta hP)
    linarith [one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)]
  have h4 : 1 ≤ (mSize M σK σB σT + n * Theta n M σK σB σT) * C_DN n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le h1 (one_le_C_DN hP)
  unfold C_DX
  linarith

theorem one_le_C_DT (hP : Params n τ M σK σB σT) : 1 ≤ C_DT n M σK σB σT := by
  have hn := hP.one_le_cast
  have h2 : 1 ≤ mSize M σK σB σT ^ 2 := one_le_pow₀ one_le_mSize
  have h1 : 1 ≤ 4 * (n : ℝ) * mSize M σK σB σT ^ 2 * C_DX n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) h2) (one_le_C_DX hP)
  have h3 : 1 ≤ 2 * (n : ℝ) * C_DN n M σK σB σT * C_X n M σK σB σT :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_C_DN hP)) (one_le_C_X hP)
  unfold C_DT
  linarith

theorem one_le_c_step (hP : Params n τ M σK σB σT) : 1 ≤ c_step n τ M σK σB σT := by
  have hΘ : 1 ≤ Theta n M σK σB σT ^ 4 := one_le_pow₀ (one_le_Theta hP)
  have hs := one_le_C_sym hP
  have hmax : 1 ≤ max (C_sym n τ M σK σB σT)
      (2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT) :=
    hs.trans (le_max_left _ _)
  unfold c_step
  exact one_le_mul_of_one_le_of_one_le (by linarith) hmax

theorem one_le_c_sum (hP : Params n τ M σK σB σT) : 1 ≤ c_sum n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have hΘ : 1 ≤ Theta n M σK σB σT ^ 2 := one_le_pow₀ (one_le_Theta hP)
  have hmax : 1 ≤ max (n : ℝ) (max (C_B n M σK σB σT)
      (mSize M σK σB σT ^ 2 * C_DT n M σK σB σT)) := hn.trans (le_max_left _ _)
  unfold c_sum
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_C_DK hP)) hmax

theorem one_le_c_star (hP : Params n τ M σK σB σT) (μ : ℝ) :
    1 ≤ c_star n τ M σK σB σT μ := by
  have h1 : 1 ≤ (2 : ℝ) ^ (2 * aExp n τ) :=
    Real.one_le_rpow (by norm_num) (by linarith [four_le_aExp hP])
  unfold c_star
  exact (one_le_mul_of_one_le_of_one_le h1 (one_le_C_E hP)).trans (le_max_left _ _)

theorem delta0_pos {ρ ρinf : ℝ} (hρinf : ρinf < ρ) : 0 < delta0 ρ ρinf :=
  lt_min one_pos (by linarith)

theorem delta0_le_one (ρ ρinf : ℝ) : delta0 ρ ρinf ≤ 1 := min_le_left _ _

theorem eight_mul_delta0_le (ρ ρinf : ℝ) : 8 * delta0 ρ ρinf ≤ ρ - ρinf := by
  have : delta0 ρ ρinf ≤ (ρ - ρinf) / 8 := min_le_right _ _
  linarith

/-- Blueprint `bp:p2:constants` (claims): the constants are `≥ 1`; `κ ≥ 1`, `a ≥ 4`;
`δ₀ ∈ (0, 1]`. Dependences are the argument lists. -/
theorem constants_spec (hP : Params n τ M σK σB σT) :
    1 ≤ cR n τ ∧ 1 ≤ mSize M σK σB σT ∧ 1 ≤ Theta n M σK σB σT ∧ 1 ≤ C_X n M σK σB σT ∧
    1 ≤ C_T n M σK σB σT ∧ 1 ≤ C_Omega n τ M σK σB σT ∧ 1 ≤ C_sym n τ M σK σB σT ∧
    1 ≤ C_red n M σK σB σT ∧ 1 ≤ C_xi0 n τ M σK σB σT ∧ 1 ≤ C_xiN n τ M σK σB σT ∧
    1 ≤ C_g n τ M σK σB σT ∧ 1 ≤ C_xi n τ M σK σB σT ∧ 1 ≤ C_DK n τ M σK σB σT ∧
    1 ≤ C_lin n τ M σK σB σT ∧ 1 ≤ C_E n τ M σK σB σT ∧ 1 ≤ C_G n M σK σB σT ∧
    1 ≤ C_B n M σK σB σT ∧ 1 ≤ C_DN n M σK σB σT ∧ 1 ≤ C_DX n M σK σB σT ∧
    1 ≤ C_DT n M σK σB σT ∧ 1 ≤ c_step n τ M σK σB σT ∧ 1 ≤ c_sum n τ M σK σB σT ∧
    1 ≤ kappa n τ ∧ 4 ≤ aExp n τ ∧
    (∀ μ, 0 < μ → 1 ≤ c_star n τ M σK σB σT μ) ∧
    (∀ ρ ρinf, 0 < ρinf → ρinf < ρ → 0 < delta0 ρ ρinf ∧ delta0 ρ ρinf ≤ 1) :=
  ⟨one_le_cR, one_le_mSize, one_le_Theta hP, one_le_C_X hP, one_le_C_T hP, one_le_C_Omega hP,
    one_le_C_sym hP, one_le_C_red hP, one_le_C_xi0 hP, one_le_C_xiN hP, one_le_C_g hP,
    one_le_C_xi hP, one_le_C_DK hP, one_le_C_lin hP, one_le_C_E hP, one_le_C_G hP, one_le_C_B hP,
    one_le_C_DN hP, one_le_C_DX hP, one_le_C_DT hP, one_le_c_step hP, one_le_c_sum hP,
    one_le_kappa hP, four_le_aExp hP, fun μ _ => one_le_c_star hP μ,
    fun _ _ _ h => ⟨delta0_pos h, delta0_le_one _ _⟩⟩

/-! ### Orderings between the constants (`step:p2:pt-small`) -/

theorem two_mul_n_mul_mSize_le_C_DN (hP : Params n τ M σK σB σT) :
    2 * (n : ℝ) * mSize M σK σB σT ≤ C_DN n M σK σB σT := by
  have h : 0 ≤ mSize M σK σB σT * C_B n M σK σB σT :=
    mul_nonneg (zero_le_one.trans one_le_mSize) (zero_le_one.trans (one_le_C_B hP))
  unfold C_DN
  linarith

theorem mSize_mul_C_B_le_C_DN (hP : Params n τ M σK σB σT) :
    mSize M σK σB σT * C_B n M σK σB σT ≤ C_DN n M σK σB σT := by
  have h : 0 ≤ 2 * (n : ℝ) * mSize M σK σB σT := by
    have := hP.one_le_cast
    have := one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
    positivity
  unfold C_DN
  linarith

theorem C_G_le_mSize_mul_C_B (hP : Params n τ M σK σB σT) :
    C_G n M σK σB σT ≤ mSize M σK σB σT * C_B n M σK σB σT := by
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have h3 : 1 ≤ mSize M σK σB σT ^ 3 := one_le_pow₀ hm
  have hG := zero_le_one.trans (one_le_C_G hP)
  calc C_G n M σK σB σT = 1 * C_G n M σK σB σT := (one_mul _).symm
    _ ≤ (2 * mSize M σK σB σT ^ 3) * C_G n M σK σB σT :=
        mul_le_mul_of_nonneg_right (by linarith) hG
    _ = mSize M σK σB σT * C_B n M σK σB σT := by unfold C_B; ring

theorem C_DN_le_C_DT (hP : Params n τ M σK σB σT) :
    C_DN n M σK σB σT ≤ C_DT n M σK σB σT := by
  have hn := hP.one_le_cast
  have hDN := zero_le_one.trans (one_le_C_DN hP)
  have hX := one_le_C_X hP
  have h1 : 0 ≤ 4 * (n : ℝ) * mSize M σK σB σT ^ 2 * C_DX n M σK σB σT := by
    have := zero_le_one.trans (one_le_C_DX hP)
    have := one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
    positivity
  have h2 : C_DN n M σK σB σT ≤ 2 * (n : ℝ) * C_DN n M σK σB σT * C_X n M σK σB σT :=
    calc C_DN n M σK σB σT = 1 * C_DN n M σK σB σT := (one_mul _).symm
      _ ≤ (2 * n * C_X n M σK σB σT) * C_DN n M σK σB σT :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [one_le_mul_of_one_le_of_one_le hn hX]) hDN
      _ = 2 * (n : ℝ) * C_DN n M σK σB σT * C_X n M σK σB σT := by ring
  unfold C_DT
  linarith

theorem n_le_C_DT (hP : Params n τ M σK σB σT) : (n : ℝ) ≤ C_DT n M σK σB σT := by
  have hn := hP.one_le_cast
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have h := two_mul_n_mul_mSize_le_C_DN hP
  have h2 : (n : ℝ) ≤ 2 * n * mSize M σK σB σT := by nlinarith
  exact (h2.trans h).trans (C_DN_le_C_DT hP)

theorem C_G_le_C_DT (hP : Params n τ M σK σB σT) : C_G n M σK σB σT ≤ C_DT n M σK σB σT :=
  ((C_G_le_mSize_mul_C_B hP).trans (mSize_mul_C_B_le_C_DN hP)).trans (C_DN_le_C_DT hP)

theorem one_le_mSize_mul_C_DT (hP : Params n τ M σK σB σT) :
    1 ≤ mSize M σK σB σT * C_DT n M σK σB σT :=
  one_le_mul_of_one_le_of_one_le one_le_mSize (one_le_C_DT hP)

/-- The coefficient `4 n 𝔪 · n + 2 n · 𝔪 ≤ C_G` of `step:p2:pt-gram`. -/
theorem gram_coeff_le (hP : Params n τ M σK σB σT) :
    4 * (n : ℝ) * mSize M σK σB σT * n + 2 * n * mSize M σK σB σT ≤ C_G n M σK σB σT := by
  have hn := hP.one_le_cast
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  unfold C_G
  nlinarith [mul_pos (zero_lt_one.trans_le hn) (zero_lt_one.trans_le hm)]

/-- Consequences of the smallness hypothesis of Lemma `bp:p2:perturbation`
(`step:p2:pt-small`): with `d / δ ≤ d / δ²`,
`n d/δ ≤ 𝔪`, `𝔪 C_G d/δ ≤ 1/2`, `C_ΔN d/δ ≤ 𝔪²` and `𝔪 C_ΔT d/δ² ≤ 1/2`. -/
theorem perturbation_small (hP : Params n τ M σK σB σT) {δ d : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 ≤ d)
    (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    (n : ℝ) * d / δ ≤ mSize M σK σB σT ∧
    mSize M σK σB σT * C_G n M σK σB σT * d / δ ≤ 1 / 2 ∧
    C_DN n M σK σB σT * d / δ ≤ mSize M σK σB σT ^ 2 ∧
    mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1 / 2 := by
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have hm0 : 0 < mSize M σK σB σT := zero_lt_one.trans_le hm
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hδδ : δ ^ 2 ≤ δ := by nlinarith
  -- `m C_DT d / δ² ≤ 1/2`
  have h4 : mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1 / 2 := by
    have : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 =
        2 * (mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2) := by ring
    linarith
  set q := mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 with hq
  have hq0 : 0 ≤ q := by
    have := zero_le_one.trans (one_le_C_DT hP)
    positivity
  -- general step: `c d / δ ≤ c d / δ²` and `c ≤ C_DT` gives `m c d / δ ≤ q`
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ C_DT n M σK σB σT →
      mSize M σK σB σT * c * d / δ ≤ q := by
    intro c hc hcC
    have h1 : mSize M σK σB σT * c * d / δ ≤ mSize M σK σB σT * c * d / δ ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) hδ2 hδδ
    have h2 : mSize M σK σB σT * c * d / δ ^ 2 ≤ q := by
      apply div_le_div_of_nonneg_right _ hδ2.le
      apply mul_le_mul_of_nonneg_right _ hd
      exact mul_le_mul_of_nonneg_left hcC hm0.le
    exact h1.trans h2
  have hG : mSize M σK σB σT * C_G n M σK σB σT * d / δ ≤ 1 / 2 :=
    (key _ (zero_le_one.trans (one_le_C_G hP)) (C_G_le_C_DT hP)).trans h4
  have hn : (n : ℝ) * d / δ ≤ mSize M σK σB σT := by
    have h := key n (by linarith [hP.one_le_cast]) (n_le_C_DT hP)
    have hnm : mSize M σK σB σT * n * d / δ = mSize M σK σB σT * ((n : ℝ) * d / δ) := by ring
    -- `m (n d / δ) ≤ 1/2`, so `n d / δ ≤ 1/(2m) ≤ m`
    have h' : mSize M σK σB σT * ((n : ℝ) * d / δ) ≤ 1 / 2 := by
      rw [← hnm]; exact h.trans h4
    nlinarith [div_nonneg (mul_nonneg (zero_le_one.trans hP.one_le_cast) hd) hδ.le]
  have hN : C_DN n M σK σB σT * d / δ ≤ mSize M σK σB σT ^ 2 := by
    have h := key _ (zero_le_one.trans (one_le_C_DN hP)) (C_DN_le_C_DT hP)
    have hnm : mSize M σK σB σT * C_DN n M σK σB σT * d / δ =
        mSize M σK σB σT * (C_DN n M σK σB σT * d / δ) := by ring
    have h' : mSize M σK σB σT * (C_DN n M σK σB σT * d / δ) ≤ 1 / 2 := by
      rw [← hnm]; exact h.trans h4
    nlinarith [div_nonneg (mul_nonneg (zero_le_one.trans (one_le_C_DN hP)) hd) hδ.le]
  exact ⟨hn, hG, hN, h4⟩

/-- The sum of `step:p2:pt-xn`: for `δ ≤ 1`,
`2 𝔪³ d + 𝔪 C_ΔN d/δ + n Θ C_ΔN d/δ² ≤ C_ΔX d/δ²`. -/
theorem pt_xn_sum_le (hP : Params n τ M σK σB σT) {δ d : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 ≤ d) :
    2 * mSize M σK σB σT ^ 3 * d + mSize M σK σB σT * C_DN n M σK σB σT * d / δ +
      n * Theta n M σK σB σT * C_DN n M σK σB σT * d / δ ^ 2 ≤
        C_DX n M σK σB σT * d / δ ^ 2 := by
  have hm0 : 0 < mSize M σK σB σT := zero_lt_one.trans_le one_le_mSize
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hδδ : δ ^ 2 ≤ δ := by nlinarith
  have hDN := zero_le_one.trans (one_le_C_DN hP)
  have h1 : 2 * mSize M σK σB σT ^ 3 * d ≤ 2 * mSize M σK σB σT ^ 3 * d / δ ^ 2 := by
    rw [le_div_iff₀ hδ2]
    have : 0 ≤ 2 * mSize M σK σB σT ^ 3 * d := by positivity
    nlinarith
  have h2 : mSize M σK σB σT * C_DN n M σK σB σT * d / δ ≤
      mSize M σK σB σT * C_DN n M σK σB σT * d / δ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hδ2 hδδ
  have h3 : C_DX n M σK σB σT * d / δ ^ 2 =
      2 * mSize M σK σB σT ^ 3 * d / δ ^ 2 + mSize M σK σB σT * C_DN n M σK σB σT * d / δ ^ 2 +
        n * Theta n M σK σB σT * C_DN n M σK σB σT * d / δ ^ 2 := by
    unfold C_DX
    ring
  rw [h3]
  linarith

/-! ### Absorption of powers of `γ` and `δ` (`cor-absorb`, `st-small`, `ne-total`) -/

/-- `γ δ^j ≤ Θ` for `γ ≤ Θ`, `δ ≤ 1`, `j ≥ 0` (`step:p2:cor-absorb`). -/
theorem mul_rpow_le {γ Θ δ j : ℝ} (hγ : 0 < γ) (hγΘ : γ ≤ Θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hj : 0 ≤ j) : γ * δ ^ j ≤ Θ := by
  have h : δ ^ j ≤ 1 := Real.rpow_le_one hδ.le hδ1 hj
  calc γ * δ ^ j ≤ γ * 1 := mul_le_mul_of_nonneg_left h hγ.le
    _ ≤ Θ := by linarith

/-- Absorption: if `0 < γ ≤ Θ`, `0 < δ ≤ 1`, `i ≤ k` and `j ≤ J`, then
`x / (γ^i δ^j) ≤ Θ^(k-i) x / (γ^k δ^J)`. -/
theorem div_absorb {γ Θ δ x j J : ℝ} {i k : ℕ} (hγ : 0 < γ) (hγΘ : γ ≤ Θ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hik : i ≤ k) (hjJ : j ≤ J) (hx : 0 ≤ x) :
    x / (γ ^ i * δ ^ j) ≤ Θ ^ (k - i) * x / (γ ^ k * δ ^ J) := by
  have hγk : γ ^ k = γ ^ i * γ ^ (k - i) := by
    rw [← pow_add]; congr 1; omega
  have hδJ : δ ^ J = δ ^ j * δ ^ (J - j) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hg : γ ^ (k - i) ≤ Θ ^ (k - i) := pow_le_pow_left₀ hγ.le hγΘ _
  have hd : δ ^ (J - j) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
  have hγi : 0 < γ ^ i := pow_pos hγ _
  have hδj : 0 < δ ^ j := Real.rpow_pos_of_pos hδ _
  have hγd : 0 < γ ^ (k - i) := pow_pos hγ _
  have hδd : 0 < δ ^ (J - j) := Real.rpow_pos_of_pos hδ _
  have hprod : γ ^ (k - i) * δ ^ (J - j) ≤ Θ ^ (k - i) :=
    calc γ ^ (k - i) * δ ^ (J - j) ≤ Θ ^ (k - i) * 1 :=
          mul_le_mul hg hd hδd.le ((pow_nonneg hγ.le _).trans hg)
      _ = Θ ^ (k - i) := mul_one _
  rw [hγk, hδJ, div_le_div_iff₀ (mul_pos hγi hδj) (mul_pos (mul_pos hγi hγd) (mul_pos hδj hδd))]
  calc x * (γ ^ i * γ ^ (k - i) * (δ ^ j * δ ^ (J - j)))
      = (x * (γ ^ i * δ ^ j)) * (γ ^ (k - i) * δ ^ (J - j)) := by ring
    _ ≤ (x * (γ ^ i * δ ^ j)) * Θ ^ (k - i) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hx (mul_pos hγi hδj).le)
    _ = Θ ^ (k - i) * x * (γ ^ i * δ ^ j) := by ring

/-- The form of `div_absorb` used with a constant: if `Θ^(k-i) X ≤ c` then
`X ε / (γ^i δ^j) ≤ c ε / (γ^k δ^J)`. -/
theorem absorb_mul_le {γ Θ δ ε X c j J : ℝ} {i k : ℕ} (hγ : 0 < γ) (hγΘ : γ ≤ Θ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hik : i ≤ k) (hjJ : j ≤ J) (hε : 0 ≤ ε) (hX : 0 ≤ X)
    (hc : Θ ^ (k - i) * X ≤ c) :
    X * ε / (γ ^ i * δ ^ j) ≤ c * ε / (γ ^ k * δ ^ J) := by
  refine (div_absorb hγ hγΘ hδ hδ1 hik hjJ (mul_nonneg hX hε)).trans ?_
  apply div_le_div_of_nonneg_right _ (mul_pos (pow_pos hγ _) (Real.rpow_pos_of_pos hδ _)).le
  calc Θ ^ (k - i) * (X * ε) = (Θ ^ (k - i) * X) * ε := by ring
    _ ≤ c * ε := mul_le_mul_of_nonneg_right hc hε

/-! ### Dominance of `c_step`, `c_sum`, `c_star` -/

theorem two_mul_pow_mul_le_aux {Θ X Y : ℝ} {p : ℕ} (hΘ : 1 ≤ Θ) (hp : p ≤ 4) (hX : 0 ≤ X)
    (hXY : X ≤ Y) : 2 * Θ ^ p * X ≤ 2 * Θ ^ 4 * Y := by
  have h1 : Θ ^ p ≤ Θ ^ 4 := pow_le_pow_right₀ hΘ hp
  have h0 : 0 ≤ Θ ^ 4 := pow_nonneg (zero_le_one.trans hΘ) 4
  calc 2 * Θ ^ p * X ≤ 2 * Θ ^ 4 * X :=
        mul_le_mul_of_nonneg_right (by linarith) hX
    _ ≤ 2 * Θ ^ 4 * Y := mul_le_mul_of_nonneg_left hXY (by linarith)

/-- `2 Θ³ C_sym ≤ 𝔠_step`. -/
theorem two_Theta_pow_three_mul_C_sym_le_c_step (hP : Params n τ M σK σB σT) :
    2 * Theta n M σK σB σT ^ 3 * C_sym n τ M σK σB σT ≤ c_step n τ M σK σB σT := by
  unfold c_step
  exact two_mul_pow_mul_le_aux (one_le_Theta hP) (by norm_num)
    (zero_le_one.trans (one_le_C_sym hP)) (le_max_left _ _)

/-- `2 Θ² C_ΔK ≤ 𝔠_step`. -/
theorem two_Theta_sq_mul_C_DK_le_c_step (hP : Params n τ M σK σB σT) :
    2 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT ≤ c_step n τ M σK σB σT := by
  have hK := one_le_C_DK hP
  have hmC := one_le_mSize_mul_C_DT hP
  have hle : C_DK n τ M σK σB σT ≤
      2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT := by
    calc C_DK n τ M σK σB σT = 1 * C_DK n τ M σK σB σT := (one_mul _).symm
      _ ≤ (2 * (mSize M σK σB σT * C_DT n M σK σB σT)) * C_DK n τ M σK σB σT :=
          mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hK)
      _ = _ := by ring
  unfold c_step
  exact two_mul_pow_mul_le_aux (one_le_Theta hP) (by norm_num) (zero_le_one.trans hK)
    (hle.trans (le_max_right _ _))

/-- `4 Θ² (𝔪 C_ΔT C_ΔK) ≤ 𝔠_step`. -/
theorem four_Theta_sq_mul_le_c_step (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 *
      (mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT) ≤
        c_step n τ M σK σB σT := by
  have hK := zero_le_one.trans (one_le_C_DK hP)
  have hmC := zero_le_one.trans (one_le_mSize_mul_C_DT hP)
  have h := two_mul_pow_mul_le_aux (Θ := Theta n M σK σB σT) (p := 2) (one_le_Theta hP)
    (by norm_num)
    (X := 2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT)
    (by
      have : 0 ≤ mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT :=
        mul_nonneg hmC hK
      linarith)
    (Y := max (C_sym n τ M σK σB σT)
      (2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT))
    (le_max_right _ _)
  unfold c_step
  calc 4 * Theta n M σK σB σT ^ 2 *
        (mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT)
      = 2 * Theta n M σK σB σT ^ 2 *
          (2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT) := by ring
    _ ≤ _ := h

theorem four_Theta_sq_mul_C_DK_le_c_sum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT ≤ c_sum n τ M σK σB σT := by
  have hn := hP.one_le_cast
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT := by
    have := zero_le_one.trans (one_le_C_DK hP)
    have := zero_le_one.trans (one_le_Theta hP)
    positivity
  unfold c_sum
  calc 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT
      = 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hn.trans (le_max_left _ _)) h0

theorem four_Theta_sq_mul_n_mul_C_DK_le_c_sum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 * ((n : ℝ) * C_DK n τ M σK σB σT) ≤ c_sum n τ M σK σB σT := by
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT := by
    have := zero_le_one.trans (one_le_C_DK hP)
    have := zero_le_one.trans (one_le_Theta hP)
    positivity
  unfold c_sum
  calc 4 * Theta n M σK σB σT ^ 2 * ((n : ℝ) * C_DK n τ M σK σB σT)
      = 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT * n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) h0

theorem four_Theta_sq_mul_C_B_mul_C_DK_le_c_sum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 * (C_B n M σK σB σT * C_DK n τ M σK σB σT) ≤
      c_sum n τ M σK σB σT := by
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT := by
    have := zero_le_one.trans (one_le_C_DK hP)
    have := zero_le_one.trans (one_le_Theta hP)
    positivity
  unfold c_sum
  calc 4 * Theta n M σK σB σT ^ 2 * (C_B n M σK σB σT * C_DK n τ M σK σB σT)
      = 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT * C_B n M σK σB σT := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        ((le_max_left _ _).trans (le_max_right _ _)) h0

theorem four_Theta_sq_mul_mSize_sq_mul_le_c_sum (hP : Params n τ M σK σB σT) :
    4 * Theta n M σK σB σT ^ 2 *
      (mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT) ≤
        c_sum n τ M σK σB σT := by
  have h0 : 0 ≤ 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT := by
    have := zero_le_one.trans (one_le_C_DK hP)
    have := zero_le_one.trans (one_le_Theta hP)
    positivity
  unfold c_sum
  calc 4 * Theta n M σK σB σT ^ 2 *
        (mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT)
      = 4 * Theta n M σK σB σT ^ 2 * C_DK n τ M σK σB σT *
          (mSize M σK σB σT ^ 2 * C_DT n M σK σB σT) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_right _ _)) h0

theorem two_rpow_mul_C_E_le_c_star (μ : ℝ) :
    (2 : ℝ) ^ (2 * aExp n τ) * C_E n τ M σK σB σT ≤ c_star n τ M σK σB σT μ :=
  le_max_left _ _

theorem c_step_mul_max_le_c_star (μ : ℝ) :
    c_step n τ M σK σB σT * max 1 (2 / μ) ≤ c_star n τ M σK σB σT μ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem two_mul_c_sum_div_le_c_star (μ : ℝ) :
    2 * c_sum n τ M σK σB σT / μ ≤ c_star n τ M σK σB σT μ :=
  (le_max_right _ _).trans (le_max_right _ _)

/-! ### Smallness of the KAM step (`step:p2:st-small`) -/

/-- The three consequences of the smallness hypothesis of Proposition `bp:p2:step`
(`step:p2:st-small`): for `d = C_ΔK ε / (γ² δ^a)`, `C_sym ε/(γ δ^(κ+1)) ≤ 1/2`, `d ≤ β/2` and
`2 𝔪 C_ΔT d/δ² ≤ 1/2`. The hypothesis `γ ≤ Θ` is Lemma `bp:p2:frequency`. -/
theorem step_small (hP : Params n τ M σK σB σT) {γ δ ε β : ℝ} (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hsmall : c_step n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ min 1 β) :
    C_sym n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ≤ 1 / 2 ∧
    C_DK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ≤ β / 2 ∧
    2 * mSize M σK σB σT * C_DT n M σK σB σT *
      (C_DK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) / δ ^ 2 ≤ 1 / 2 := by
  have ha := eight_le_aExp hP
  have hκ : aExp n τ = 2 * kappa n τ + 2 := rfl
  have hQ1 : c_step n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ 1 :=
    hsmall.trans (min_le_left _ _)
  have hQβ : c_step n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) ≤ β :=
    hsmall.trans (min_le_right _ _)
  have hhalf : ∀ c : ℝ, c = c_step n τ M σK σB σT / 2 →
      c * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) =
        c_step n τ M σK σB σT * ε / (γ ^ 4 * δ ^ (2 * aExp n τ)) / 2 := by
    intro c hc
    rw [hc]; ring
  refine ⟨?_, ?_, ?_⟩
  · have h := absorb_mul_le (i := 1) (k := 4) (j := kappa n τ + 1) (J := 2 * aExp n τ)
      (c := c_step n τ M σK σB σT / 2) hγ hγΘ hδ hδ1 (by norm_num) (by linarith) hε
      (zero_le_one.trans (one_le_C_sym hP))
      (by have := two_Theta_pow_three_mul_C_sym_le_c_step hP; norm_num; linarith)
    rw [hhalf _ rfl, pow_one] at h
    linarith
  · have h := absorb_mul_le (i := 2) (k := 4) (j := aExp n τ) (J := 2 * aExp n τ)
      (c := c_step n τ M σK σB σT / 2) hγ hγΘ hδ hδ1 (by norm_num) (by linarith) hε
      (zero_le_one.trans (one_le_C_DK hP))
      (by have := two_Theta_sq_mul_C_DK_le_c_step hP; norm_num; linarith)
    rw [hhalf _ rfl] at h
    linarith
  · have hrw : 2 * mSize M σK σB σT * C_DT n M σK σB σT *
        (C_DK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) / δ ^ 2 =
        (2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT) * ε /
          (γ ^ 2 * δ ^ (aExp n τ + 2)) := by
      rw [Real.rpow_add hδ, Real.rpow_two]
      field_simp
    have hX : 0 ≤ 2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT := by
      have := zero_le_one.trans (one_le_mSize_mul_C_DT hP)
      have := zero_le_one.trans (one_le_C_DK hP)
      have h2 : 2 * mSize M σK σB σT * C_DT n M σK σB σT * C_DK n τ M σK σB σT =
          2 * (mSize M σK σB σT * C_DT n M σK σB σT) * C_DK n τ M σK σB σT := by ring
      rw [h2]
      positivity
    have h := absorb_mul_le (i := 2) (k := 4) (j := aExp n τ + 2) (J := 2 * aExp n τ)
      (c := c_step n τ M σK σB σT / 2) hγ hγΘ hδ hδ1 (by norm_num) (by linarith) hε hX
      (by
        have := four_Theta_sq_mul_le_c_step hP
        norm_num
        nlinarith)
    rw [hhalf _ rfl] at h
    rw [hrw]
    linarith

/-! ### The induction: error decay, summed bounds, step smallness (`bp:p2:iteration`) -/

/-- The hypothesis of Lemma `bp:p2:error-decay` from `𝔠_* e / (γ⁴ δ₀^{2a}) ≤ 1`, since
`𝔠_* ≥ 2^{2a} C_E`. (`step:p2:it-sums`, first sentence.) -/
theorem error_decay_hyp {γ d0 e μ : ℝ} (hγ : 0 < γ) (hd0 : 0 < d0) (he : 0 ≤ e)
    (hsmall : c_star n τ M σK σB σT μ * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    (2 : ℝ) ^ (2 * aExp n τ) * C_E n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1 := by
  refine le_trans ?_ hsmall
  apply div_le_div_of_nonneg_right _ (mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)).le
  exact mul_le_mul_of_nonneg_right (two_rpow_mul_C_E_le_c_star μ) he

/-- `𝔠_sum e / (γ⁴ δ₀^{2a}) ≤ μ/2` from `𝔠_* e / (γ⁴ δ₀^{2a}) ≤ 1`, since
`𝔠_* ≥ 2 𝔠_sum / μ`. -/
theorem c_sum_small {γ d0 e μ : ℝ} (hγ : 0 < γ) (hd0 : 0 < d0) (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : c_star n τ M σK σB σT μ * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    c_sum n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ μ / 2 := by
  have hD : 0 < γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)
  have h1 : 2 * c_sum n τ M σK σB σT ≤ c_star n τ M σK σB σT μ * μ :=
    (div_le_iff₀ hμ).1 (two_mul_c_sum_div_le_c_star μ)
  have h2 : c_sum n τ M σK σB σT * e ≤ (μ / 2) * (c_star n τ M σK σB σT μ * e) := by
    have := mul_le_mul_of_nonneg_right h1 he
    nlinarith
  have h3 : c_star n τ M σK σB σT μ * e ≤ γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    (div_le_one hD).1 hsmall
  rw [div_le_iff₀ hD]
  calc c_sum n τ M σK σB σT * e ≤ (μ / 2) * (c_star n τ M σK σB σT μ * e) := h2
    _ ≤ (μ / 2) * (γ ^ 4 * d0 ^ (2 * aExp n τ)) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)

/-- `step:p2:it-stepsmall`: `𝔠_step e / (γ⁴ δ₀^{2a}) ≤ min {1, μ/2}`, since
`𝔠_* ≥ 𝔠_step max {1, 2/μ}`. -/
theorem iteration_step_small (hP : Params n τ M σK σB σT) {γ d0 e μ : ℝ} (hγ : 0 < γ)
    (hd0 : 0 < d0) (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : c_star n τ M σK σB σT μ * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    c_step n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ min 1 (μ / 2) := by
  have hD : 0 < γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hd0 _)
  have hc0 := zero_le_one.trans (one_le_c_step hP)
  have h3 : c_star n τ M σK σB σT μ * e ≤ γ ^ 4 * d0 ^ (2 * aExp n τ) :=
    (div_le_one hD).1 hsmall
  have hmax := c_step_mul_max_le_c_star (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB)
    (σT := σT) μ
  have hA : c_step n τ M σK σB σT ≤ c_star n τ M σK σB σT μ :=
    le_trans (le_mul_of_one_le_right hc0 (le_max_left _ _)) hmax
  have hB : c_step n τ M σK σB σT * (2 / μ) ≤ c_star n τ M σK σB σT μ :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0) hmax
  refine le_min ?_ ?_
  · rw [div_le_one hD]
    exact (mul_le_mul_of_nonneg_right hA he).trans h3
  · rw [div_le_iff₀ hD]
    have h4 : c_step n τ M σK σB σT * (2 / μ) * e ≤ γ ^ 4 * d0 ^ (2 * aExp n τ) :=
      (mul_le_mul_of_nonneg_right hB he).trans h3
    have h5 : c_step n τ M σK σB σT * e = (μ / 2) * (c_step n τ M σK σB σT * (2 / μ) * e) := by
      field_simp
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 (by linarith)

/-- The summed bounds of `step:p2:it-sums`. For a coefficient `X ≥ 0` with
`4 Θ² X ≤ 𝔠_sum` and an exponent `j ≤ 2a`, `(X/γ²) · (2e/δ₀^j) ≤ μ/4`. Here `2e/δ₀^j` is the bound
of `∑_s ε_s/δ_s^j` of Lemma `bp:p2:error-decay`. -/
theorem sum_coef_le {γ d0 e μ X j : ℝ} (hγ : 0 < γ) (hγΘ : γ ≤ Theta n M σK σB σT)
    (hd0 : 0 < d0) (hd01 : d0 ≤ 1) (he : 0 ≤ e) (hμ : 0 < μ) (hX : 0 ≤ X)
    (hXc : 4 * Theta n M σK σB σT ^ 2 * X ≤ c_sum n τ M σK σB σT) (hj : j ≤ 2 * aExp n τ)
    (hsmall : c_star n τ M σK σB σT μ * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    X / γ ^ 2 * (2 * e / d0 ^ j) ≤ μ / 4 := by
  have hrw : X / γ ^ 2 * (2 * e / d0 ^ j) = (2 * X) * e / (γ ^ 2 * d0 ^ j) := by
    have : d0 ^ j ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
    field_simp
  have hcs : c_sum n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ μ / 2 :=
    c_sum_small hγ hd0 he hμ hsmall
  have h := absorb_mul_le (i := 2) (k := 4) (X := 2 * X) (j := j) (J := 2 * aExp n τ)
    (c := c_sum n τ M σK σB σT / 2) hγ hγΘ hd0 hd01 (by norm_num) hj he (by linarith)
    (by simp only [show (4 - 2 : ℕ) = 2 from rfl]; linarith)
  have h2 : c_sum n τ M σK σB σT / 2 * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) =
      c_sum n τ M σK σB σT * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) / 2 := by ring
  rw [hrw]
  rw [h2] at h
  linarith

/-- The four summed bounds of `step:p2:it-sums`, in the form
`coefficient / γ² · (2e/δ₀^j) ≤ …`, for `j = a, a+1, a+1, a+2`, namely the bounds for
`∑ d_s`, `∑ n d_s/δ_s`, `∑ C_B d_s/δ_s` and `∑ 2𝔪² C_ΔT d_s/δ_s²`. -/
theorem iteration_sums (hP : Params n τ M σK σB σT) {γ d0 e μ : ℝ} (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hd0 : 0 < d0) (hd01 : d0 ≤ 1) (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : c_star n τ M σK σB σT μ * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    C_DK n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ aExp n τ) ≤ μ / 4 ∧
    (n : ℝ) * C_DK n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ (aExp n τ + 1)) ≤ μ / 4 ∧
    C_B n M σK σB σT * C_DK n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ (aExp n τ + 1)) ≤ μ / 4 ∧
    2 * mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT / γ ^ 2 *
      (2 * e / d0 ^ (aExp n τ + 2)) ≤ μ / 2 := by
  have ha := eight_le_aExp hP
  have hn := zero_le_one.trans hP.one_le_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sum_coef_le hγ hγΘ hd0 hd01 he hμ (zero_le_one.trans (one_le_C_DK hP))
      (four_Theta_sq_mul_C_DK_le_c_sum hP) (by linarith) hsmall
  · have h := sum_coef_le (X := (n : ℝ) * C_DK n τ M σK σB σT) (j := aExp n τ + 1) hγ hγΘ hd0
      hd01 he hμ (mul_nonneg hn (zero_le_one.trans (one_le_C_DK hP)))
      (four_Theta_sq_mul_n_mul_C_DK_le_c_sum hP) (by linarith) hsmall
    exact h
  · exact sum_coef_le (X := C_B n M σK σB σT * C_DK n τ M σK σB σT) (j := aExp n τ + 1) hγ hγΘ
      hd0 hd01 he hμ (mul_nonneg (zero_le_one.trans (one_le_C_B hP))
        (zero_le_one.trans (one_le_C_DK hP)))
      (four_Theta_sq_mul_C_B_mul_C_DK_le_c_sum hP) (by linarith) hsmall
  · have hY : 0 ≤ mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT := by
      have := zero_le_one.trans (one_le_C_DT hP)
      have := zero_le_one.trans (one_le_C_DK hP)
      have := zero_le_one.trans (one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT))
      positivity
    have h := sum_coef_le
      (X := mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT)
      (j := aExp n τ + 2) hγ hγΘ hd0 hd01 he hμ hY
      (four_Theta_sq_mul_mSize_sq_mul_le_c_sum hP) (by linarith) hsmall
    have heq : 2 * mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT / γ ^ 2 *
        (2 * e / d0 ^ (aExp n τ + 2)) =
        2 * (mSize M σK σB σT ^ 2 * C_DT n M σK σB σT * C_DK n τ M σK σB σT / γ ^ 2 *
          (2 * e / d0 ^ (aExp n τ + 2))) := by ring
    rw [heq]
    linarith

/-- The closeness bound of Proposition `bp:p2:limit`(c):
`2 C_ΔK e / (γ² δ₀^a) ≤ μ/4`. -/
theorem closeness_le (hP : Params n τ M σK σB σT) {γ d0 e μ : ℝ} (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (hd0 : 0 < d0) (hd01 : d0 ≤ 1) (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : c_star n τ M σK σB σT μ * e / (γ ^ 4 * d0 ^ (2 * aExp n τ)) ≤ 1) :
    2 * C_DK n τ M σK σB σT * e / (γ ^ 2 * d0 ^ aExp n τ) ≤ μ / 4 := by
  have h := (iteration_sums hP hγ hγΘ hd0 hd01 he hμ hsmall).1
  have hd : d0 ^ aExp n τ ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
  have heq : C_DK n τ M σK σB σT / γ ^ 2 * (2 * e / d0 ^ aExp n τ) =
      2 * C_DK n τ M σK σB σT * e / (γ ^ 2 * d0 ^ aExp n τ) := by
    field_simp
  rw [← heq]
  exact h

/-! ### Proof of Theorem G1 (`step:p2:g1-e`) -/

/-- `step:p2:g1-e` for abstract data: from `C₁ e / (γ⁴ ρ^{4τ}) < 1`, with
`C₁ = ρ^{4τ} max {γ̄⁴, c δ₀^{-2a}}`, `0 < γ ≤ γ̄` and `c ≥ 0`, we get `e < 1` and
`c e / (γ⁴ δ₀^{2a}) < 1`. -/
theorem g1_error_small_aux {ρ γ γbar e c d0 τ' a : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ)
    (hγγbar : γ ≤ γbar) (hd0 : 0 < d0) (hc : 0 ≤ c)
    (h : ρ ^ (4 * τ') * max (γbar ^ 4) (c * d0 ^ (-(2 * a))) * e / (γ ^ 4 * ρ ^ (4 * τ')) < 1) :
    e < 1 ∧ c * e / (γ ^ 4 * d0 ^ (2 * a)) < 1 := by
  have hP : 0 < ρ ^ (4 * τ') := Real.rpow_pos_of_pos hρ _
  have hD : 0 < d0 ^ (2 * a) := Real.rpow_pos_of_pos hd0 _
  have hγ4 : 0 < γ ^ 4 := pow_pos hγ 4
  have hγbar0 : 0 < γbar := hγ.trans_le hγγbar
  have hγbar4 : 0 < γbar ^ 4 := pow_pos hγbar0 4
  set Mx := max (γbar ^ 4) (c * d0 ^ (-(2 * a))) with hMx
  have h1 : Mx * e < γ ^ 4 := by
    have hrw : ρ ^ (4 * τ') * Mx * e / (γ ^ 4 * ρ ^ (4 * τ')) = Mx * e / γ ^ 4 := by
      field_simp
    rw [hrw, div_lt_one hγ4] at h
    exact h
  have hneg : d0 ^ (-(2 * a)) = (d0 ^ (2 * a))⁻¹ := Real.rpow_neg hd0.le _
  rcases le_or_gt e 0 with he | he
  · refine ⟨by linarith, ?_⟩
    have : c * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc he
    have h0 : c * e / (γ ^ 4 * d0 ^ (2 * a)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg this (mul_pos hγ4 hD).le
    linarith
  · constructor
    · have h2 : γbar ^ 4 * e ≤ Mx * e := mul_le_mul_of_nonneg_right (le_max_left _ _) he.le
      have h3 : γ ^ 4 ≤ γbar ^ 4 := pow_le_pow_left₀ hγ.le hγγbar 4
      have : γbar ^ 4 * e < γbar ^ 4 * 1 := by linarith
      exact lt_of_mul_lt_mul_left this hγbar4.le
    · have h2 : c * d0 ^ (-(2 * a)) * e ≤ Mx * e :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) he.le
      rw [div_lt_one (mul_pos hγ4 hD)]
      have h4 : c * e = (c * d0 ^ (-(2 * a)) * e) * d0 ^ (2 * a) := by
        rw [hneg]; field_simp
      rw [h4]
      exact mul_lt_mul_of_pos_right (lt_of_le_of_lt h2 h1) hD

/-- `step:p2:g1-e`: the hypothesis `C₁ e/(γ⁴ ρ^{4τ}) < 1` of Theorem `bp:p2:g1`, with
`C₁ = ρ^{4τ} max {γ̄⁴, 𝔠_* δ₀^{-2a}}`, gives `e < 1` and `𝔠_* e/(γ⁴ δ₀^{2a}) < 1`. -/
theorem g1_error_small (hP : Params n τ M σK σB σT) {ρ ρinf γ γbar μ e : ℝ} (hρinf : 0 < ρinf)
    (hρ : ρinf < ρ) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (h : ρ ^ (4 * τ) * max (γbar ^ 4) (c_star n τ M σK σB σT μ *
      delta0 ρ ρinf ^ (-(2 * aExp n τ))) * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1) :
    e < 1 ∧ c_star n τ M σK σB σT μ * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) < 1 :=
  g1_error_small_aux (hρinf.trans hρ) hγ hγγbar (delta0_pos hρ)
    (zero_le_one.trans (one_le_c_star hP μ)) h

/-- `step:p2:g1-check`: `2 C_ΔK e/(γ² δ₀^a) = C₂ e/(γ² ρ^{2τ})` with
`C₂ = 2 C_ΔK ρ^{2τ} δ₀^{-a}`. -/
theorem g1_closeness_eq {ρ γ d0 C e τ' a : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hd0 : 0 < d0) :
    2 * C * e / (γ ^ 2 * d0 ^ a) =
      2 * C * ρ ^ (2 * τ') * d0 ^ (-a) * e / (γ ^ 2 * ρ ^ (2 * τ')) := by
  have h1 : ρ ^ (2 * τ') ≠ 0 := (Real.rpow_pos_of_pos hρ _).ne'
  have h2 : d0 ^ a ≠ 0 := (Real.rpow_pos_of_pos hd0 _).ne'
  rw [Real.rpow_neg hd0.le]
  field_simp

end KAM.Apost

end
