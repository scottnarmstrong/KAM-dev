/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellIter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: shell errors tend to zero (blueprint `bpW:w8:etor`)

Blueprint label `bpW:w8:etor` (milestone W8).

`w8_etor`: for every shell `n`, `e^{(n)}_tor ≤ E₄ κ_n = E₅ t_n^{1/64} ≤ 7/256` and
`ε^{(n)}_ω ≤ α_n/(70 L_A) ≤ α_n` (the W8 constants at the W5–W6 constants `w8Upstream m hm`).
Pure arithmetic in the constants of W6 (`bpW:w6:constants`), W7 (`θ₀ ≤ 1/(8L_A)`, `L_A > 1`) and
W8 (`bpW:w8:const`, `bpW:w8:shell-data` (i)).
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Wave

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

/-- `θ₀ ≤ 1/(8 L_A)` (W7 (C4)). -/
theorem measTheta0_le_inv_eight_LA : measTheta0 m hm ≤ 1 / (8 * measLA m hm) := by
  have hL := measLA_pos m hm
  unfold measTheta0
  calc (measLA m hm)⁻¹ * min (1 / 8) (measSigmaX m hm / (2 * (measKstar m hm + 2)))
      ≤ (measLA m hm)⁻¹ * (1 / 8) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ = 1 / (8 * measLA m hm) := by field_simp

/-- `L_A > 1` (W7 `bpW:w7:freqcoords` (ii): `L_A = (8π/21) λ₂(4λ₁ + 3λ₂)`). -/
theorem one_lt_measLA : 1 < measLA m hm := by
  obtain ⟨h0, -, h1⟩ := measLam_facts m hm
  have hπ := Real.pi_gt_three
  unfold measLA
  have : 10 < 4 * lamTan m hm 0 + 3 * lamTan m hm 1 := by linarith
  have h8 : 1 < 8 * π / 21 * 2 := by nlinarith
  calc (1 : ℝ) < 8 * π / 21 * 2 * 10 := by nlinarith
    _ ≤ 8 * π / 21 * lamTan m hm 1 * (4 * lamTan m hm 0 + 3 * lamTan m hm 1) := by
        have : 0 < 8 * π / 21 := by positivity
        gcongr

/-- `x^{1-53} = (x^{52})⁻¹`, `x^{1-52} = (x^{51})⁻¹` for the W5–W6 exponents `t^♮ = 53`,
`t = 52`. -/
theorem w8_rpow_one_sub_exp {x : ℝ} (hx : 0 < x) :
    x ^ (1 - w6Tn) = (x ^ 52)⁻¹ ∧ x ^ (1 - w6T) = (x ^ 51)⁻¹ := by
  rw [w6Tn_eq, w6T_eq]
  constructor
  · rw [show (1 : ℝ) - 53 = -((52 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]
  · rw [show (1 : ℝ) - 52 = -((51 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]

/-- **Shell errors tend to zero** (blueprint `bpW:w8:etor`): for every `n`,
`e^{(n)}_tor ≤ E₄ κ_n = E₅ t_n^{1/64} ≤ 7/256` and `ε^{(n)}_ω ≤ α_n/(70 L_A) ≤ α_n`. -/
theorem w8_etor (n : ℕ) :
    w8ShellEtor m hm n ≤ w8E4 (w8Upstream m hm) * w8kappa m hm (w8Upstream m hm) 𝔱 n ∧
      w8E4 (w8Upstream m hm) * w8kappa m hm (w8Upstream m hm) 𝔱 n =
        w8E5 m hm (w8Upstream m hm) * w8tn 𝔱 n ^ (1 / 64 : ℝ) ∧
      w8E5 m hm (w8Upstream m hm) * w8tn 𝔱 n ^ (1 / 64 : ℝ) ≤ 7 / 256 ∧
      w8ShellEpsOm m hm n ≤ w8alpha 𝔱 n / (70 * measLA m hm) ∧
      w8alpha 𝔱 n / (70 * measLA m hm) ≤ w8alpha 𝔱 n := by
  set u := w8Upstream m hm
  have hT := w8T0_pos hm u
  obtain ⟨⟨h1, -, -⟩, ⟨-, hαt⟩, -, -, hκ1, -, -, -⟩ := w8_shellData_sizes hm u n
  obtain ⟨-, -, -, -, h5⟩ := w8tn_facts hm u n
  obtain ⟨-, -, hα, -, -, hε, -, -⟩ := w8_shellData_prep hm n
  have ht1 : w8tn 𝔱 n ≤ 1 := (w8tn_facts hm u n).2.2.2.1
  have hα1 : w8alpha 𝔱 n ≤ 1 := hαt.trans ht1
  set α := w8alpha 𝔱 n
  set ε := w8epsSharp m hm 𝔱 n
  set κ := w8kappa m hm u 𝔱 n with hκdef
  have hγ := w6Gamma_pos m hm
  have hγ1 := w6Gamma1_pos m hm
  have hκ0 : 0 < κ := by rw [hκdef, w8kappa]; exact div_pos hε (mul_pos u.gam_pos hα)
  have hc : 0 < alphaCheck α := Real.rpow_pos_of_pos hα _
  have hεα : ε / α = κ * w6Gamma m hm := by
    rw [hκdef, w8kappa]
    show ε / α = ε / (w6Gamma m hm * α) * w6Gamma m hm
    field_simp
  have hκ43 : κ ^ (4 / 3 : ℝ) ≤ κ := by
    calc κ ^ (4 / 3 : ℝ) ≤ κ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hκ0 hκ1 (by norm_num)
      _ = κ := Real.rpow_one κ
  have hσP := w8_rpow_one_sub_exp w6SigmaP_pos
  have hσ0 := w8_rpow_one_sub_exp w6Sigma0_pos
  have hCFn := w6CFn_pos
  have hCF := w6CF_pos
  have hsP : 0 < (w6SigmaP ^ 52)⁻¹ := by have := w6SigmaP_pos; positivity
  have hs0 : 0 < (w6Sigma0 ^ 51)⁻¹ := by have := w6Sigma0_pos; positivity
  -- `e_tor ≤ E₄ κ`
  have hE : w8ShellEtor m hm n ≤ w8E4 u * κ := by
    have hM := w6MFP_le hα hα1 hε.le
    rw [hσP.1, hεα] at hM
    have hP := w6WaveSeq_ePhi (m := m) (hm := hm) hα (w8rn 𝔱 n) ε (w8Eps0W m hm n)
    rw [hσ0.2] at hP
    have he0 : w8Eps0W m hm n / alphaCheck α = κ ^ (4 / 3 : ℝ) * w6Gamma1 m hm := by
      show κ ^ (4 / 3 : ℝ) * w6Gamma1 m hm * alphaCheck α / alphaCheck α = _
      field_simp
    rw [he0] at hP
    have hP' : (w6WaveSeq m hm α (w8rn 𝔱 n) ε (w8Eps0W m hm n)).ePhi ≤
        5 * w6CF * (w6Sigma0 ^ 51)⁻¹ * (κ * w6Gamma1 m hm) := by
      rw [hP]; gcongr
    have e4 : w8E4 u * κ = w6CFn * (w6SigmaP ^ 52)⁻¹ * (κ * w6Gamma m hm) +
        5 * w6CF * (w6Sigma0 ^ 51)⁻¹ * (κ * w6Gamma1 m hm) := by
      unfold w8E4; rw [w8SigmaP_eq_w6, w8Sigma0_eq_w6]
      show (w6CFn * w6Gamma m hm * (w6SigmaP ^ 52)⁻¹ +
        5 * w6CF * w6Gamma1 m hm * (w6Sigma0 ^ 51)⁻¹) * κ = _
      ring
    rw [e4]
    unfold w8ShellEtor w6Etor
    linarith
  -- `E₄ κ = E₅ t_n^{1/64}`
  have hE45 : w8E4 u * κ = w8E5 m hm u * w8tn 𝔱 n ^ (1 / 64 : ℝ) := by
    rw [hκdef, w8kappa_eq m hm u hT]
    unfold w8E5
    have := u.gam_pos
    field_simp
    rfl
  -- `E₅ t_n^{1/64} ≤ 7/256`
  have hE5 := w8E5_pos hm u
  have hq : w8T0 m hm u ^ (1 / 64 : ℝ) ≤ 7 / (256 * w8E5 m hm u) :=
    rpow_one_div_64_le_of_le_pow hT.le (by positivity) (w8T0_le hm u).2.2.2.2
  have h7 : w8E5 m hm u * w8tn 𝔱 n ^ (1 / 64 : ℝ) ≤ 7 / 256 := by
    calc w8E5 m hm u * w8tn 𝔱 n ^ (1 / 64 : ℝ)
        ≤ w8E5 m hm u * (7 / (256 * w8E5 m hm u)) := by gcongr; exact h5.trans hq
      _ = 7 / 256 := by field_simp
  -- `ε_ω ≤ α_n/(70 L_A)`
  have hL := measLA_pos m hm
  have hL1 := one_lt_measLA hm
  have hθ := measTheta0_le_inv_eight_LA hm
  have hM := w6M_pos m hm
  have hθ0 := w6MeasTheta0_pos m hm
  have hB : measTheta0 m hm / (425 * (1 + w6M m hm)) ≤ 1 / (3400 * measLA m hm) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : measTheta0 m hm * (8 * measLA m hm) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hθ; linarith
    nlinarith
  have hg := (w6Gamma_le_theta m hm).trans hB
  have hg1 := (w6Gamma1_le_theta m hm).trans hB
  have hcα : alphaCheck α ≤ α := by
    calc alphaCheck α ≤ α ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
      _ = α := Real.rpow_one α
  have he0 : w8Eps0W m hm n ≤ w6Gamma1 m hm * α :=
    (w8_epsFlat_shell hm n).2.2.trans (mul_le_mul_of_nonneg_left hcα hγ1.le)
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hom : w8ShellEpsOm m hm n ≤ α / (70 * measLA m hm) := by
    unfold w8ShellEpsOm
    have hsum : 6 * π * w6Gamma m hm * α + 8 * π * w8Eps0W m hm n ≤
        14 * π * (1 / (3400 * measLA m hm)) * α := by
      have a1 : 6 * π * w6Gamma m hm * α ≤ 6 * π * (1 / (3400 * measLA m hm)) * α := by gcongr
      have a2 : 8 * π * w8Eps0W m hm n ≤ 8 * π * (1 / (3400 * measLA m hm)) * α := by
        calc 8 * π * w8Eps0W m hm n ≤ 8 * π * (w6Gamma1 m hm * α) := by gcongr
          _ ≤ 8 * π * ((1 / (3400 * measLA m hm)) * α) := by gcongr
          _ = _ := by ring
      linarith
    refine hsum.trans ?_
    rw [show 14 * π * (1 / (3400 * measLA m hm)) * α = 14 * π / 3400 * (α / measLA m hm) by
      field_simp, show α / (70 * measLA m hm) = 1 / 70 * (α / measLA m hm) by field_simp]
    have : 0 ≤ α / measLA m hm := by positivity
    have h14 : 14 * π / 3400 ≤ 1 / 70 := by linarith
    exact mul_le_mul_of_nonneg_right h14 this
  refine ⟨hE, hE45, h7, hom, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end KAM.Wave

end
