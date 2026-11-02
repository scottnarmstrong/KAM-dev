/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Data
public import KAM.Wave.KamSupport.KamSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# W6: the iteration sequences (blueprint `bpW:w6:sequences`)

Blueprint label `bpW:w6:sequences` (milestone W6).

Fixed: `τ = 24`, `t = 2τ + 4 = 52` and W5's constants `c_F`, `c₀ = 16 c_F`, `C₂ = 896 + 168 c_F`
(`stepCF`, `stepC0`, `stepC2` of `KamStep/Data`, evaluated at `τ = 24`). Given
`0 < s₀ ≤ 1`, `r₀ > 0`, `0 < α₀ ≤ 1`, `M₀ > 0`, `ε₀ > 0` (the record `W6SeqData` and its
validity `W6SeqData.SeqValid`):
`σ_ν = σ₀ 2^{-ν}` (`σ₀ = s₀/40`), `s_{ν+1} = s_ν - 5σ_ν`, `α_ν = α₀(1 + 2^{-ν})/2`,
`M_ν = M₀ (2 - 2^{-ν})`, `λ_ν = α_ν/M_ν`, `η_ν = (ε_ν/(α_ν σ_ν^t))^{1/3}`, `r_{ν+1} = η_ν r_ν`,
`ε_{ν+1} = 2 C₂ ε_ν η_ν`, `D_ν = D(s_ν, r_ν)`, `γ₀ = (2^{t+4} C₂ + c₀)^{-3}`,
`K₀ = (96 π γ₀ σ₀^t)^{-1/(τ+1)}`, `K_ν = K₀ 2^ν`, `K_{-1} = 0`.

Results: `s_ν ↓ 3s₀/4`, `σ_ν ≤ min (1/4, s_ν/6)`, `λ_ν ≥ λ₀/4`, `K₀ ≥ 1`, `K_ν ≥ 2^ν`, and the
identity `ε_{ν+1} = 2C₂ ε_ν^{4/3}/(α_ν σ_ν^t)^{1/3}`.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.Wave

/-! ### Fixed constants -/

/-- `τ = 24` (blueprint `bpW:w6`, Notation). -/
def w6Tau : ℝ := 24

/-- `t = 2τ + 4 = 52` (blueprint `bpW:w6`, Notation). -/
def w6T : ℝ := stepExpT w6Tau

/-- W5's `c_F = 9 C₁ b_W(24)` (`bpW:w5:ledger`). -/
def w6CF : ℝ := stepCF w6Tau

/-- W5's `c₀ = 16 c_F` (`bpW:w5:ledger`). -/
def w6C0 : ℝ := stepC0 w6Tau

/-- W5's `C₂ = 896 + 168 c_F` (`bpW:w5:ledger`). -/
def w6C2 : ℝ := stepC2 w6Tau

/-- `γ₀ = (2^{t+4} C₂ + c₀)^{-3}` (blueprint `bpW:w6:sequences`). -/
def w6Gamma0 : ℝ := ((2 : ℝ) ^ (w6T + 4) * w6C2 + w6C0)⁻¹ ^ 3

theorem w6Tau_eq : w6Tau = 24 := rfl

theorem w6T_eq : w6T = 52 := by unfold w6T stepExpT w6Tau; norm_num

theorem w6CF_pos : 0 < w6CF := stepCF_pos (by unfold w6Tau; norm_num)

theorem w6C0_eq : w6C0 = 16 * w6CF := rfl

theorem w6C0_pos : 0 < w6C0 := by rw [w6C0_eq]; have := w6CF_pos; positivity

theorem w6C2_eq : w6C2 = 896 + 168 * w6CF := rfl

theorem w6C2_ge : 896 ≤ w6C2 := by rw [w6C2_eq]; have := w6CF_pos; linarith

theorem w6C2_pos : 0 < w6C2 := by have := w6C2_ge; linarith

theorem w6two_rpow_T4 : (2 : ℝ) ^ (w6T + 4) = 2 ^ (56 : ℕ) := by
  rw [w6T_eq, show (52 : ℝ) + 4 = ((56 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The base `X = 2^{t+4} C₂ + c₀` of `γ₀ = X^{-3}`. -/
def w6GammaBase : ℝ := (2 : ℝ) ^ (w6T + 4) * w6C2 + w6C0

theorem w6Gamma0_eq : w6Gamma0 = w6GammaBase⁻¹ ^ 3 := rfl

theorem w6GammaBase_ge : (2 : ℝ) ^ (56 : ℕ) * w6C2 + w6C0 ≤ w6GammaBase := by
  rw [w6GammaBase, w6two_rpow_T4]

theorem w6GammaBase_ge_big : (2 : ℝ) ^ (56 : ℕ) * 896 ≤ w6GammaBase := by
  have h := w6GammaBase_ge; have := w6C0_pos; have := w6C2_ge
  have : (2 : ℝ) ^ (56 : ℕ) * 896 ≤ (2 : ℝ) ^ (56 : ℕ) * w6C2 :=
    mul_le_mul_of_nonneg_left this (by positivity)
  linarith

theorem w6GammaBase_pos : 0 < w6GammaBase := lt_of_lt_of_le (by positivity) w6GammaBase_ge_big

theorem w6Gamma0_pos : 0 < w6Gamma0 := by
  rw [w6Gamma0_eq]; have := w6GammaBase_pos; positivity

/-- `γ₀^{1/3} = X⁻¹`. -/
theorem w6Gamma0_rpow_third : w6Gamma0 ^ (1 / 3 : ℝ) = w6GammaBase⁻¹ := by
  rw [w6Gamma0_eq, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 w6GammaBase_pos.le)]
  norm_num

/-- `γ₀ ≤ X⁻¹` (as `X ≥ 1`). -/
theorem w6Gamma0_le_inv : w6Gamma0 ≤ w6GammaBase⁻¹ := by
  rw [w6Gamma0_eq]
  have h1 : 1 ≤ w6GammaBase := le_trans (by norm_num) w6GammaBase_ge_big
  have h0 : 0 ≤ w6GammaBase⁻¹ := inv_nonneg.2 (by linarith)
  have h2 : w6GammaBase⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  calc w6GammaBase⁻¹ ^ 3 ≤ w6GammaBase⁻¹ ^ 1 :=
        pow_le_pow_of_le_one h0 h2 (by norm_num)
    _ = w6GammaBase⁻¹ := pow_one _

theorem w6Gamma0_le_small : w6Gamma0 ≤ ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ :=
  w6Gamma0_le_inv.trans (inv_anti₀ (by positivity) w6GammaBase_ge_big)

/-! ### The data and the sequences -/

/-- The free data of Definition `bpW:w6:sequences`: `s₀, r₀, α₀, M₀, ε₀`. -/
structure W6SeqData where
  /-- `s₀` -/
  s0 : ℝ
  /-- `r₀` -/
  r0 : ℝ
  /-- `α₀` -/
  al0 : ℝ
  /-- `M₀` -/
  M0 : ℝ
  /-- `ε₀` -/
  eps0 : ℝ

/-- The standing conditions `0 < s₀ ≤ 1`, `r₀ > 0`, `0 < α₀ ≤ 1`, `M₀ > 0`, `ε₀ > 0`. -/
structure W6SeqData.SeqValid (d : W6SeqData) : Prop where
  s0_pos : 0 < d.s0
  s0_le : d.s0 ≤ 1
  r0_pos : 0 < d.r0
  al0_pos : 0 < d.al0
  al0_le : d.al0 ≤ 1
  M0_pos : 0 < d.M0
  eps0_pos : 0 < d.eps0

namespace W6SeqData

variable (d : W6SeqData)

/-- `σ_ν = σ₀ 2^{-ν}`, `σ₀ = s₀/40`. -/
def sigma (ν : ℕ) : ℝ := d.s0 / 40 / 2 ^ ν

/-- `s_0 = s₀`, `s_{ν+1} = s_ν - 5 σ_ν`. -/
def s : ℕ → ℝ
  | 0 => d.s0
  | ν + 1 => s ν - 5 * d.sigma ν

/-- `α_ν = (α₀/2)(1 + 2^{-ν})`. -/
def alpha (ν : ℕ) : ℝ := d.al0 / 2 * (1 + 1 / 2 ^ ν)

/-- `M_ν = M₀ (2 - 2^{-ν})`. -/
def Mnu (ν : ℕ) : ℝ := d.M0 * (2 - 1 / 2 ^ ν)

/-- `λ_ν = α_ν / M_ν`. -/
def lam (ν : ℕ) : ℝ := d.alpha ν / d.Mnu ν

/-- The cube root `(e/(a σ^t))^{1/3}` defining `η`. -/
def etaOf (e a σ : ℝ) : ℝ := (e / (a * σ ^ w6T)) ^ (1 / 3 : ℝ)

/-- `ε_0 = ε₀`, `ε_{ν+1} = 2 C₂ ε_ν η_ν`. -/
def eps : ℕ → ℝ
  | 0 => d.eps0
  | ν + 1 => 2 * w6C2 * eps ν * etaOf (eps ν) (d.alpha ν) (d.sigma ν)

/-- `η_ν = (ε_ν/(α_ν σ_ν^t))^{1/3}`. -/
def etaNu (ν : ℕ) : ℝ := etaOf (d.eps ν) (d.alpha ν) (d.sigma ν)

/-- `r_0 = r₀`, `r_{ν+1} = η_ν r_ν`. -/
def rNu : ℕ → ℝ
  | 0 => d.r0
  | ν + 1 => d.etaNu ν * rNu ν

/-- `q_ν = ε_ν/(α_ν σ_ν^t)` (blueprint `bpW:w6:iter-lemma`). -/
def qNu (ν : ℕ) : ℝ := d.eps ν / (d.alpha ν * d.sigma ν ^ w6T)

/-- `D_ν = D(s_ν, r_ν)`. -/
def domNu (ν : ℕ) : Set KamPhase := kamDomain (d.s ν) (d.rNu ν)

/-- `K₀ = (96 π γ₀ σ₀^t)^{-1/(τ+1)}`. -/
def K0 : ℝ := (96 * π * w6Gamma0 * d.sigma 0 ^ w6T) ^ (-(1 / (w6Tau + 1)))

/-- `K_ν = K₀ 2^ν`. -/
def K (ν : ℕ) : ℝ := d.K0 * 2 ^ ν

/-- `K_{ν-1}`, with `K_{-1} = 0`. -/
def KprevNu : ℕ → ℝ
  | 0 => 0
  | ν + 1 => d.K ν

/-- `s_∞ = 3 s₀/4`. -/
def sInfty : ℝ := 3 / 4 * d.s0

theorem eps_succ (ν : ℕ) : d.eps (ν + 1) = 2 * w6C2 * d.eps ν * d.etaNu ν := rfl

theorem rNu_succ (ν : ℕ) : d.rNu (ν + 1) = d.etaNu ν * d.rNu ν := rfl

theorem sigma_zero : d.sigma 0 = d.s0 / 40 := by simp [sigma]

theorem sigma_succ (ν : ℕ) : d.sigma (ν + 1) = d.sigma ν / 2 := by
  unfold sigma; rw [pow_succ]; ring

theorem alpha_zero : d.alpha 0 = d.al0 := by simp [alpha]; ring

theorem M_zero : d.Mnu 0 = d.M0 := by simp [Mnu]; ring

theorem eta_eq_q (ν : ℕ) : d.etaNu ν = d.qNu ν ^ (1 / 3 : ℝ) := rfl

/-- Closed form `s_ν = s₀ - 10 σ₀ (1 - 2^{-ν})`. -/
theorem s_eq (ν : ℕ) : d.s ν = d.s0 - 10 * (d.s0 / 40) * (1 - 1 / 2 ^ ν) := by
  induction ν with
  | zero => simp [s]
  | succ n ih =>
    simp only [s, ih, sigma]
    rw [pow_succ]
    field_simp
    ring

section valid

variable {d}
variable (hd : d.SeqValid)
include hd

theorem sigmaNu_pos (ν : ℕ) : 0 < d.sigma ν := by
  unfold sigma; have := hd.s0_pos; positivity

theorem alpha_pos (ν : ℕ) : 0 < d.alpha ν := by
  unfold alpha; have := hd.al0_pos; positivity

theorem M_pos (ν : ℕ) : 0 < d.Mnu ν := by
  unfold Mnu
  have := hd.M0_pos
  have h : 1 / (2 : ℝ) ^ ν ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have : 0 < 2 - 1 / (2 : ℝ) ^ ν := by linarith
  positivity

theorem lam_pos (ν : ℕ) : 0 < d.lam ν := div_pos (alpha_pos hd ν) (M_pos hd ν)

theorem alphaNu_le (ν : ℕ) : d.alpha ν ≤ d.al0 := by
  unfold alpha
  have := hd.al0_pos
  have h : 1 / (2 : ℝ) ^ ν ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  nlinarith

theorem half_le_alpha (ν : ℕ) : d.al0 / 2 ≤ d.alpha ν := by
  unfold alpha
  have := hd.al0_pos
  have : 0 ≤ 1 / (2 : ℝ) ^ ν := by positivity
  nlinarith

theorem M_le (ν : ℕ) : d.Mnu ν ≤ 2 * d.M0 := by
  unfold Mnu
  have := hd.M0_pos
  have : 0 ≤ 1 / (2 : ℝ) ^ ν := by positivity
  nlinarith

/-- `λ_ν ≥ λ₀/4` (blueprint `bpW:w6:sequences`). -/
theorem lam_ge (ν : ℕ) : d.lam 0 / 4 ≤ d.lam ν := by
  unfold lam
  rw [alpha_zero, M_zero]
  have h1 := half_le_alpha hd ν
  have h2 := M_le hd ν
  have hM := M_pos hd ν
  have h0 := hd.M0_pos
  have ha := hd.al0_pos
  rw [div_le_div_iff₀ (by positivity) hM]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- `s_ν ≥ s_∞ = 3s₀/4`. -/
theorem sInf_le_s (ν : ℕ) : d.sInfty ≤ d.s ν := by
  rw [s_eq, sInfty]
  have := hd.s0_pos
  have : 0 ≤ 1 / (2 : ℝ) ^ ν := by positivity
  nlinarith

/-- `s_ν` is antitone. -/
theorem s_antitone : Antitone d.s := by
  refine antitone_nat_of_succ_le fun ν => ?_
  show d.s ν - 5 * d.sigma ν ≤ d.s ν
  have := sigmaNu_pos hd ν; linarith

omit hd in
/-- `s_ν → s_∞ = 3s₀/4`. -/
theorem s_tendsto : Tendsto d.s atTop (𝓝 d.sInfty) := by
  have h : Tendsto (fun ν : ℕ => 1 / (2 : ℝ) ^ ν) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Tendsto (fun ν : ℕ => d.s0 - 10 * (d.s0 / 40) * (1 - 1 / (2 : ℝ) ^ ν)) atTop
      (𝓝 (d.s0 - 10 * (d.s0 / 40) * (1 - 0))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_const_nhds.sub h))
  have he : d.s0 - 10 * (d.s0 / 40) * (1 - 0) = d.sInfty := by rw [sInfty]; ring
  rw [he] at h2
  exact h2.congr fun ν => (s_eq d ν).symm

theorem sigma_le_sigma0 (ν : ℕ) : d.sigma ν ≤ d.s0 / 40 := by
  unfold sigma
  have := hd.s0_pos
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

/-- `σ_ν ≤ 1/4`. -/
theorem sigma_le_quarter (ν : ℕ) : d.sigma ν ≤ 1 / 4 := by
  have := sigma_le_sigma0 hd ν; have := hd.s0_le; linarith

/-- `σ_ν ≤ s_ν/6`. -/
theorem sigma_le_s_div_six (ν : ℕ) : d.sigma ν ≤ d.s ν / 6 := by
  have h1 := sigma_le_sigma0 hd ν; have h2 := sInf_le_s hd ν
  rw [sInfty] at h2; have := hd.s0_pos; linarith

/-- `σ_ν ≤ min (1/4) (s_ν/6)` (blueprint `bpW:w6:sequences`). -/
theorem sigma_le_min (ν : ℕ) : d.sigma ν ≤ min (1 / 4) (d.s ν / 6) :=
  le_min (sigma_le_quarter hd ν) (sigma_le_s_div_six hd ν)

theorem sigma_rpow_le_one (ν : ℕ) : d.sigma ν ^ w6T ≤ 1 := by
  have h0 := sigmaNu_pos hd ν
  have h1 : d.sigma ν ≤ 1 := by have := sigma_le_quarter hd ν; linarith
  exact Real.rpow_le_one h0.le h1 (by rw [w6T_eq]; norm_num)

/-- `96 π γ₀ σ₀^t ≤ 1`. -/
theorem K0_base_le_one : 96 * π * w6Gamma0 * d.sigma 0 ^ w6T ≤ 1 := by
  have hγ := w6Gamma0_le_small
  have hγ0 := w6Gamma0_pos
  have hσ := sigma_rpow_le_one hd 0
  have hσ0 : 0 ≤ d.sigma 0 ^ w6T := Real.rpow_nonneg (sigmaNu_pos hd 0).le _
  have hπ := Real.pi_le_four
  have hpi0 := Real.pi_pos
  have h1 : 96 * π * w6Gamma0 ≤ 1 := by
    have : (96 : ℝ) * π * ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; norm_num; nlinarith
    calc 96 * π * w6Gamma0 ≤ 96 * π * ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ := by gcongr
      _ ≤ 1 := this
  calc 96 * π * w6Gamma0 * d.sigma 0 ^ w6T ≤ 1 * 1 :=
        mul_le_mul h1 hσ hσ0 zero_le_one
    _ = 1 := one_mul 1

theorem K0_base_pos : 0 < 96 * π * w6Gamma0 * d.sigma 0 ^ w6T := by
  have := w6Gamma0_pos; have := Real.pi_pos
  have := Real.rpow_pos_of_pos (sigmaNu_pos hd 0) w6T
  positivity

/-- `K₀ ≥ 1` (blueprint `bpW:w6:sequences`). -/
theorem one_le_K0 : 1 ≤ d.K0 := by
  unfold K0
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (K0_base_pos hd) (K0_base_le_one hd)
  rw [w6Tau_eq]; norm_num

/-- `K_ν ≥ 2^ν` (blueprint `bpW:w6:sequences`). -/
theorem two_pow_le_K (ν : ℕ) : (2 : ℝ) ^ ν ≤ d.K ν := by
  unfold K
  have := one_le_K0 hd
  have : (0 : ℝ) < 2 ^ ν := by positivity
  nlinarith

theorem KNu_pos (ν : ℕ) : 0 < d.K ν := lt_of_lt_of_le (by positivity) (two_pow_le_K hd ν)

/-- `ε_{ν+1} = 2C₂ ε_ν^{κ}/(α_ν σ_ν^t)^{κ-1}`, `κ = 4/3` (blueprint `bpW:w6:sequences`), for
`ε_ν ≥ 0`. -/
theorem eps_succ_eq_kappa (ν : ℕ) (he : 0 ≤ d.eps ν) :
    d.eps (ν + 1) =
      2 * w6C2 * d.eps ν ^ (4 / 3 : ℝ) / (d.alpha ν * d.sigma ν ^ w6T) ^ (4 / 3 - 1 : ℝ) := by
  have hb : 0 < d.alpha ν * d.sigma ν ^ w6T :=
    mul_pos (alpha_pos hd ν) (Real.rpow_pos_of_pos (sigmaNu_pos hd ν) _)
  rw [eps_succ, etaNu, etaOf, Real.div_rpow he hb.le]
  have h43 : d.eps ν ^ (4 / 3 : ℝ) = d.eps ν * d.eps ν ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num]
    rcases he.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (by norm_num)]; simp
    · rw [Real.rpow_add h, Real.rpow_one]
  rw [h43, show (4 / 3 - 1 : ℝ) = 1 / 3 by norm_num]
  ring

end valid

end W6SeqData

end KAM.Wave
