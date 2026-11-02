/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Sequences
public import KAM.Wave.Measure.Pair
public import KAM.Wave.Homological.Wave
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# W6: the constants (blueprint `bpW:w6:constants`)

Blueprint label `bpW:w6:constants` (milestone W6).

In this order, after W7's constants (`measTheta0 = θ₀`, `measBetaStar = β_*`) and W5's
(`stepTn`, `stepCFn`, `stepC0n`, `stepC2n` at `τ = 24`: `t^♮ = 53`, `c^♮_F`, `c^♮_0`, `C^♮_2`):
`s = 1/8`, `σ_P = s/40`, `s₀ = s - 5σ_P = 7s/8`, `σ₀ = s₀/40`, `M = M_ω + M_Ω` (W4's
`waveMomega + waveMOmega`), `M₀ = 2M`, `γ₀` of `bpW:w6:sequences` (`w6Gamma0`),
`γ₁ = min {γ₀ σ₀^t, θ₀/(425(1+M)), β_*/8}`,
`γ = min {1/40, (c^♮_0)^{-3} σ_P^{t^♮}, θ₀/(425(1+M)), (γ₁ σ_P^{t^♮/3}/(2C^♮_2))^{3/4}}`.
All depend on `m` only.

Also the elementary consequences used by `bpW:w6:prep-step` (steps `p-data`, `p-size`),
`bpW:w6:applicable` and `bpW:w6:freq-lip` (the "where" clause: `ε_ω, ε₁, ε₂ ≤ α`, `θ ≤ θ₀`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

/-- `s = 1/8`. -/
def w6S : ℝ := 1 / 8

/-- `σ_P = s/40`. -/
def w6SigmaP : ℝ := w6S / 40

/-- `s₀ = s - 5σ_P`. -/
def w6S0 : ℝ := w6S - 5 * w6SigmaP

/-- `σ₀ = s₀/40`. -/
def w6Sigma0 : ℝ := w6S0 / 40

/-- `t^♮ = 2τ + 5 = 53`. -/
def w6Tn : ℝ := stepTn w6Tau

/-- W5's `c^♮_F = 9 C₁ b^♮(24)`. -/
def w6CFn : ℝ := stepCFn w6Tau

/-- W5's `c^♮_0 = 16 c^♮_F`. -/
def w6C0n : ℝ := stepC0n w6Tau

/-- W5's `C^♮_2 = 896 + 168 c^♮_F`. -/
def w6C2n : ℝ := stepC2n w6Tau

/-- `M = M_ω + M_Ω` of Lemma `bpW:w4:wave` (i). -/
def w6M (m : ℝ) (hm : 0 < m) : ℝ := waveMomega m hm + waveMOmega m hm

/-- `M₀ = 2M`. -/
def w6M0 (m : ℝ) (hm : 0 < m) : ℝ := 2 * w6M m hm

/-- `γ₁ = min {γ₀ σ₀^t, θ₀/(425(1+M)), β_*/8}` (blueprint `bpW:w6:constants`). -/
def w6Gamma1 (m : ℝ) (hm : 0 < m) : ℝ :=
  min (min (w6Gamma0 * w6Sigma0 ^ w6T) (measTheta0 m hm / (425 * (1 + w6M m hm))))
    (measBetaStar m / 8)

/-- `γ = min {1/40, (c^♮_0)^{-3} σ_P^{t^♮}, θ₀/(425(1+M)), (γ₁ σ_P^{t^♮/3}/(2C^♮_2))^{3/4}}`
(blueprint `bpW:w6:constants`). -/
def w6Gamma (m : ℝ) (hm : 0 < m) : ℝ :=
  min (min (min (1 / 40) (w6C0n⁻¹ ^ 3 * w6SigmaP ^ w6Tn))
    (measTheta0 m hm / (425 * (1 + w6M m hm))))
    ((w6Gamma1 m hm * w6SigmaP ^ (w6Tn / 3) / (2 * w6C2n)) ^ (3 / 4 : ℝ))

/-- The Lipschitz number `θ = 425 (1+M) max(γ, γ₁)` of Lemma `bpW:w6:freq-lip`. -/
def w6Theta (m : ℝ) (hm : 0 < m) : ℝ := 425 * (1 + w6M m hm) * max (w6Gamma m hm) (w6Gamma1 m hm)

theorem w6S0_eq : w6S0 = 7 / 8 * w6S := by unfold w6S0 w6SigmaP w6S; norm_num

theorem w6S0_val : w6S0 = 7 / 64 := by unfold w6S0 w6SigmaP w6S; norm_num

theorem w6SigmaP_val : w6SigmaP = 1 / 320 := by unfold w6SigmaP w6S; norm_num

theorem w6Sigma0_val : w6Sigma0 = 7 / 2560 := by rw [w6Sigma0, w6S0_val]; norm_num

theorem w6SigmaP_pos : 0 < w6SigmaP := by rw [w6SigmaP_val]; norm_num

theorem w6Sigma0_pos : 0 < w6Sigma0 := by rw [w6Sigma0_val]; norm_num

theorem w6Tn_eq : w6Tn = 53 := by unfold w6Tn stepTn w6Tau; norm_num

theorem w6CFn_pos : 0 < w6CFn := stepCFn_pos (by unfold w6Tau; norm_num)

theorem w6C0n_pos : 0 < w6C0n := stepC0n_pos (by unfold w6Tau; norm_num)

theorem w6C2n_pos : 0 < w6C2n := by
  unfold w6C2n stepC2n; have := w6CFn_pos; unfold w6CFn at this; linarith

section

variable (m : ℝ) (hm : 0 < m)

theorem w6M_pos : 0 < w6M m hm := by
  have h1 : 0 < lam m hm 1 := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < lam m hm 2 := Real.sqrt_pos.2 (by positivity)
  unfold w6M waveMomega waveMOmega
  positivity

theorem w6M0_pos : 0 < w6M0 m hm := by unfold w6M0; have := w6M_pos m hm; positivity

theorem w6MeasTheta0_pos : 0 < measTheta0 m hm := by
  unfold measTheta0
  have := measSigmaX_pos m hm
  have := measLA_pos m hm
  have : 0 < measKstar m hm + 2 := by linarith [measKstar_pos m hm]
  apply mul_pos (inv_pos.2 (measLA_pos m hm))
  exact lt_min (by norm_num) (by positivity)

theorem w6ThetaBound_pos : 0 < measTheta0 m hm / (425 * (1 + w6M m hm)) := by
  have := w6MeasTheta0_pos m hm; have := w6M_pos m hm; positivity

theorem w6Gamma1_pos : 0 < w6Gamma1 m hm := by
  unfold w6Gamma1
  have h1 : 0 < w6Gamma0 * w6Sigma0 ^ w6T :=
    mul_pos w6Gamma0_pos (Real.rpow_pos_of_pos w6Sigma0_pos _)
  have h2 := w6ThetaBound_pos m hm
  have h3 : 0 < measBetaStar m / 8 := by have := measBetaStar_pos hm; positivity
  exact lt_min (lt_min h1 h2) h3

theorem w6Gamma1_le_gamma0 : w6Gamma1 m hm ≤ w6Gamma0 * w6Sigma0 ^ w6T :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem w6Gamma1_le_theta : w6Gamma1 m hm ≤ measTheta0 m hm / (425 * (1 + w6M m hm)) :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem w6Gamma1_le_beta : w6Gamma1 m hm ≤ measBetaStar m / 8 := min_le_right _ _

theorem w6Gamma_pos : 0 < w6Gamma m hm := by
  unfold w6Gamma
  have h1 : 0 < w6C0n⁻¹ ^ 3 * w6SigmaP ^ w6Tn := by
    have := w6C0n_pos; have := Real.rpow_pos_of_pos w6SigmaP_pos w6Tn; positivity
  have h2 := w6ThetaBound_pos m hm
  have h3 : 0 < (w6Gamma1 m hm * w6SigmaP ^ (w6Tn / 3) / (2 * w6C2n)) ^ (3 / 4 : ℝ) := by
    have := w6Gamma1_pos m hm; have := w6C2n_pos
    have := Real.rpow_pos_of_pos w6SigmaP_pos (w6Tn / 3)
    apply Real.rpow_pos_of_pos; positivity
  exact lt_min (lt_min (lt_min (by norm_num) h1) h2) h3

theorem w6Gamma_le_fortieth : w6Gamma m hm ≤ 1 / 40 :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

theorem w6Gamma_le_c0n : w6Gamma m hm ≤ w6C0n⁻¹ ^ 3 * w6SigmaP ^ w6Tn :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))

theorem w6Gamma_le_theta : w6Gamma m hm ≤ measTheta0 m hm / (425 * (1 + w6M m hm)) :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem w6Gamma_le_prep :
    w6Gamma m hm ≤ (w6Gamma1 m hm * w6SigmaP ^ (w6Tn / 3) / (2 * w6C2n)) ^ (3 / 4 : ℝ) :=
  min_le_right _ _

/-- `θ = 425(1+M) max(γ,γ₁) ≤ θ₀` (blueprint `bpW:w6:freq-lip`). -/
theorem w6Theta_le : w6Theta m hm ≤ measTheta0 m hm := by
  have hM := w6M_pos m hm
  have hpos : 0 < 425 * (1 + w6M m hm) := by positivity
  have h : max (w6Gamma m hm) (w6Gamma1 m hm) ≤ measTheta0 m hm / (425 * (1 + w6M m hm)) :=
    max_le (w6Gamma_le_theta m hm) (w6Gamma1_le_theta m hm)
  unfold w6Theta
  calc 425 * (1 + w6M m hm) * max (w6Gamma m hm) (w6Gamma1 m hm)
      ≤ 425 * (1 + w6M m hm) * (measTheta0 m hm / (425 * (1 + w6M m hm))) :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = measTheta0 m hm := by field_simp

theorem w6Theta_nonneg : 0 ≤ w6Theta m hm := by
  unfold w6Theta
  have := w6M_pos m hm; have := w6Gamma_pos m hm
  have : 0 ≤ max (w6Gamma m hm) (w6Gamma1 m hm) := le_max_of_le_left this.le
  positivity

/-- `6πγ ≤ 1/2`. -/
theorem w6six_pi_gamma_le : 6 * π * w6Gamma m hm ≤ 1 / 2 := by
  have h := w6Gamma_le_fortieth m hm
  have := w6Gamma_pos m hm
  have hπ := Real.pi_lt_d2
  nlinarith

theorem w6Sigma0_rpow_le_one : w6Sigma0 ^ w6T ≤ 1 :=
  Real.rpow_le_one w6Sigma0_pos.le (by rw [w6Sigma0_val]; norm_num) (by rw [w6T_eq]; norm_num)

/-- `γ₁ ≤ 1/(2^{56}·896)`, a crude bound. -/
theorem w6Gamma1_le_small : w6Gamma1 m hm ≤ ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ := by
  have h := w6Gamma1_le_gamma0 m hm
  have := w6Gamma0_le_small
  have := w6Sigma0_rpow_le_one
  have := w6Gamma0_pos
  have : w6Gamma0 * w6Sigma0 ^ w6T ≤ w6Gamma0 := by
    have := Real.rpow_nonneg w6Sigma0_pos.le w6T
    nlinarith
  linarith

/-- `8πγ₁ ≤ 1/2`. -/
theorem w6eight_pi_gamma1_le : 8 * π * w6Gamma1 m hm ≤ 1 / 2 := by
  have h := w6Gamma1_le_small m hm
  have := w6Gamma1_pos m hm
  have hπ := Real.pi_lt_d2
  have : ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ ≤ 1 / 100 := by norm_num
  nlinarith

/-- `22γ ≤ 1` (blueprint `bpW:w6:prep-step`, step `p-step`: `(6π+3)ε/λ ≤ 22γM ≤ M`). -/
theorem w6twentytwo_gamma_le : 22 * w6Gamma m hm ≤ 1 := by
  have := w6Gamma_le_fortieth m hm; linarith

/-- Step `p-data` of `bpW:w6:prep-step`: `γ/σ_P^{t^♮} ≤ (c^♮_0)^{-3}`. -/
theorem w6prep_data_arith : w6Gamma m hm / w6SigmaP ^ w6Tn ≤ w6C0n⁻¹ ^ 3 := by
  have hs := Real.rpow_pos_of_pos w6SigmaP_pos w6Tn
  rw [div_le_iff₀ hs]; exact w6Gamma_le_c0n m hm

/-- Step `p-size` of `bpW:w6:prep-step`: `2 C^♮_2 γ^{4/3} σ_P^{-t^♮/3} ≤ γ₁`. -/
theorem w6prep_size_arith :
    2 * w6C2n * w6Gamma m hm ^ (4 / 3 : ℝ) / w6SigmaP ^ (w6Tn / 3) ≤ w6Gamma1 m hm := by
  have hγ := w6Gamma_pos m hm
  have hs := Real.rpow_pos_of_pos w6SigmaP_pos (w6Tn / 3)
  have hC := w6C2n_pos
  have h1 := w6Gamma1_pos m hm
  set B := w6Gamma1 m hm * w6SigmaP ^ (w6Tn / 3) / (2 * w6C2n) with hB
  have hB0 : 0 < B := by positivity
  have h := w6Gamma_le_prep m hm
  have h43 : w6Gamma m hm ^ (4 / 3 : ℝ) ≤ B := by
    calc w6Gamma m hm ^ (4 / 3 : ℝ) ≤ (B ^ (3 / 4 : ℝ)) ^ (4 / 3 : ℝ) :=
          Real.rpow_le_rpow hγ.le h (by norm_num)
      _ = B := by rw [← Real.rpow_mul hB0.le]; norm_num
  rw [div_le_iff₀ hs]
  calc 2 * w6C2n * w6Gamma m hm ^ (4 / 3 : ℝ) ≤ 2 * w6C2n * B := by gcongr
    _ = w6Gamma1 m hm * w6SigmaP ^ (w6Tn / 3) := by rw [hB]; field_simp

variable {m hm}

/-- **The arithmetic of Lemma `bpW:w6:applicable`**: for `0 < α ≤ α₀` and `α̌ = α^{48/47}`:
`γ₁ α̌ ≤ γ₀ σ₀^t α̌`, `8 γ₁ α̌ ≤ β_*`, `2γα ≤ β_*`, `α̌ ≤ β_*`. -/
theorem w6applicable_arith {α : ℝ} (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) :
    w6Gamma1 m hm * alphaCheck α ≤ w6Gamma0 * w6Sigma0 ^ w6T * alphaCheck α ∧
      8 * (w6Gamma1 m hm * alphaCheck α) ≤ measBetaStar m ∧
      2 * w6Gamma m hm * α ≤ measBetaStar m ∧ alphaCheck α ≤ measBetaStar m := by
  obtain ⟨hc0, hcα, hαh, hh27, hhβ, -⟩ := alpha_facts m hm hα hα0
  have hβ := measBetaStar_pos hm
  have hg1 := w6Gamma1_le_beta m hm
  have hg1p := w6Gamma1_pos m hm
  have hg := w6Gamma_le_fortieth m hm
  have hgp := w6Gamma_pos m hm
  refine ⟨mul_le_mul_of_nonneg_right (w6Gamma1_le_gamma0 m hm) hc0.le, ?_, ?_, ?_⟩
  · have hc1 : alphaCheck α ≤ 1 := by linarith
    nlinarith
  · nlinarith
  · linarith

/-- **The constants of Lemma `bpW:w6:freq-lip`**: for `0 < α ≤ α₀`, `0 ≤ ε ≤ γα` and
`0 ≤ ε₀ ≤ γ₁ α̌`: `ε_ω = 6πγα + 8πε₀`, `ε₁ = 3γα`, `ε₂ = 4ε₀` lie in `[0, α]` and
`θ = 425(1+M)max(γ,γ₁) ∈ [0, θ₀]`. -/
theorem w6freqLip_consts {α ε₀ : ℝ} (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hε₀ : 0 ≤ ε₀)
    (hε₀' : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) :
    6 * π * w6Gamma m hm * α + 8 * π * ε₀ ∈ Set.Icc 0 α ∧
      3 * w6Gamma m hm * α ∈ Set.Icc 0 α ∧ 4 * ε₀ ∈ Set.Icc 0 α ∧
      w6Theta m hm ∈ Set.Icc 0 (measTheta0 m hm) := by
  obtain ⟨hc0, hcα, -, -, -, -⟩ := alpha_facts m hm hα hα0
  have hg := w6Gamma_le_fortieth m hm
  have hgp := w6Gamma_pos m hm
  have hg1p := w6Gamma1_pos m hm
  have h6 := w6six_pi_gamma_le m hm
  have h8 := w6eight_pi_gamma1_le m hm
  have hπ := Real.pi_pos
  have he : ε₀ ≤ w6Gamma1 m hm * α := hε₀'.trans (mul_le_mul_of_nonneg_left hcα hg1p.le)
  have hg1s := w6Gamma1_le_small m hm
  have : ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ ≤ 1 / 100 := by norm_num
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, by nlinarith⟩, ⟨by positivity, by nlinarith⟩,
    ⟨w6Theta_nonneg m hm, w6Theta_le m hm⟩⟩
  have : 8 * π * ε₀ ≤ 8 * π * (w6Gamma1 m hm * α) := by gcongr
  nlinarith

end

end KAM.Wave
