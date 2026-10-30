/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Frozen
public import KAM.Certificate.Sound.Ham
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Rational upper bounds of the classical small-divisor constant

For `τ ∈ ℕ`, `classicalOk n τ J δ c` checks over `ℚ` that `c ≥ c♮(n, τ, δ)` (`cohConstC`):
`ζ(2, a) = Σ_{j ≥ 0} (a + j)⁻²` is bounded by `J` terms and the telescoping tail
`(a + J - 1/2)⁻¹`, `Γ(2τ+1) = (2τ)!`, and `π`, `e` by `3.141592 < π < 3.141593`, `e > 2.718281`.

`NumA.cert_of_le`: rational majorants of the classical constants at the schedule are certificates
on the whole Diophantine set (`NumA.cert_classical` with `≤` in place of `=`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Sharp2 KAM.Sharp2.RouteA KAM.Certificate

/-- A rational lower bound of `π`. -/
def piLo : ℚ := 3141592 / 1000000
/-- A rational upper bound of `π`. -/
def piUp : ℚ := 3141593 / 1000000
/-- A rational lower bound of `e`. -/
def eLo : ℚ := 2718281 / 1000000

/-- `Σ_{j<J} (a + j)⁻² + (a + J - 1/2)⁻¹ ≥ ζ(2, a)`. -/
def zetaUp (a : ℚ) (J : ℕ) : ℚ :=
  sumRangeQ J (fun j => ((a + j)⁻¹) ^ 2) + (a + J - 1 / 2)⁻¹

/-- `A_τ` from above. -/
def shellUp (τ J : ℕ) : ℚ := 2 ^ (2 * τ + 1) * zetaUp (2 ^ τ) J

/-- `ε_τ(4πδ)` from above. -/
def epsUp (τ : ℕ) (δ : ℚ) : ℚ :=
  4 * piUp * δ * (2 * (τ : ℚ) / eLo) ^ (2 * τ) / ((2 * τ).factorial : ℚ)

/-- The radicand of `c♮` from above. -/
def radUp (n τ J : ℕ) (δ : ℚ) : ℚ :=
  2 ^ n * (shellUp τ J * ((2 * τ).factorial : ℚ) * (1 + epsUp τ δ))

/-- `c ≥ c♮(n, τ, δ)`, without a square root. -/
def classicalOk (n τ J : ℕ) (δ c : ℚ) : Bool :=
  decide (0 < c) && decide (radUp n τ J δ ≤ (c * (2 * piLo) * (4 * piLo) ^ τ) ^ 2)

theorem piLo_lt : (piLo : ℝ) < Real.pi := by
  have := Real.pi_gt_d6
  simp only [piLo]; push_cast; linarith

theorem pi_lt_piUp : Real.pi < (piUp : ℝ) := by
  have := Real.pi_lt_d6
  simp only [piUp]; push_cast; linarith

theorem eLo_lt : (eLo : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9
  simp only [eLo]; push_cast; linarith

/-- The telescoping bound. -/
theorem sum_inv_sq_le {b : ℝ} (hb : 1 / 2 < b) (m : ℕ) :
    ∑ j ∈ Finset.range m, ((b + j)⁻¹) ^ 2 ≤ (b - 1 / 2)⁻¹ - (b + m - 1 / 2)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : 0 < b + m - 1 / 2 := by linarith
    have h2 : 0 < b + m + 1 / 2 := by linarith
    have h3 : 0 < b + m := by linarith
    have key : ((b + m)⁻¹) ^ 2 ≤ (b + m - 1 / 2)⁻¹ - (b + m + 1 / 2)⁻¹ := by
      have e : (b + m - 1 / 2)⁻¹ - (b + m + 1 / 2)⁻¹ =
          ((b + m - 1 / 2) * (b + m + 1 / 2))⁻¹ := by
        rw [inv_sub_inv h1.ne' h2.ne', show b + m + 1 / 2 - (b + m - 1 / 2) = 1 by ring, one_div]
      rw [e, inv_pow]
      refine inv_anti₀ (mul_pos h1 h2) ?_
      nlinarith
    have e2 : b + ((m + 1 : ℕ) : ℝ) - 1 / 2 = b + m + 1 / 2 := by push_cast; ring
    rw [e2]
    linarith

/-- `ζ(2, a) ≤ Σ_{j<J} (a + j)⁻² + (a + J - 1/2)⁻¹`. -/
theorem tsum_inv_sq_le {a : ℝ} (ha : 1 / 2 < a) (J : ℕ) :
    ∑' j : ℕ, ((a + j)⁻¹) ^ 2 ≤
      ∑ j ∈ Finset.range J, ((a + j)⁻¹) ^ 2 + (a + J - 1 / 2)⁻¹ := by
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hb : 1 / 2 < a + J := by linarith
  set g : ℕ → ℝ := fun j => ((a + (j + J : ℕ))⁻¹) ^ 2 with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    have : (0 : ℝ) ≤ ((j + J : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 < a + ((j + J : ℕ) : ℝ) := by linarith
    positivity
  have hsum : ∀ m, ∑ j ∈ Finset.range m, g j ≤ (a + J - 1 / 2)⁻¹ := fun m => by
    have h := sum_inv_sq_le hb m
    have e : ∀ j : ℕ, ((a + (j + J : ℕ))⁻¹) ^ 2 = ((a + J + j)⁻¹) ^ 2 := fun j => by
      push_cast; ring_nf
    have hp : 0 ≤ (a + J + m - 1 / 2)⁻¹ := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have : 0 < a + J + m - 1 / 2 := by linarith
      positivity
    simp only [hg, e]
    linarith
  have hs : Summable g := summable_of_sum_range_le hg0 hsum
  have hs' : Summable fun j : ℕ => ((a + j)⁻¹) ^ 2 := (summable_nat_add_iff J).1 hs
  rw [← hs'.sum_add_tsum_nat_add J]
  exact add_le_add le_rfl (Real.tsum_le_of_sum_range_le hg0 hsum)

theorem one_lt_two_pow_cast (τ : ℕ) : (1 : ℝ) / 2 < ((2 : ℝ) ^ τ) := by
  have : (1 : ℝ) ≤ 2 ^ τ := one_le_pow₀ (by norm_num)
  linarith

/-- `A_τ ≤ shellUp τ J`. -/
theorem shellConst_le_shellUp (τ J : ℕ) : shellConst τ ≤ (shellUp τ J : ℝ) := by
  have ha := one_lt_two_pow_cast τ
  have e1 : (2 : ℝ) ^ (2 * (τ : ℝ) + 1) = ((2 ^ (2 * τ + 1) : ℚ) : ℝ) := by
    have : 2 * (τ : ℝ) + 1 = ((2 * τ + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]; push_cast; rfl
  have e2 : (2 : ℝ) ^ (τ : ℝ) = (2 : ℝ) ^ τ := Real.rpow_natCast _ _
  unfold shellConst
  rw [e1, e2]
  simp only [shellUp, zetaUp, sumRangeQ_eq]
  push_cast
  refine mul_le_mul_of_nonneg_left (tsum_inv_sq_le ha J) (by positivity)

/-- `ε_τ(4πδ) ≤ epsUp τ δ`. -/
theorem sdEps_le_epsUp (τ : ℕ) {δ : ℚ} (hδ : 0 ≤ δ) :
    sdEps τ (4 * Real.pi * δ) ≤ (epsUp τ δ : ℝ) := by
  have he0 : (0 : ℝ) < (eLo : ℝ) := by simp only [eLo]; norm_num
  have hU : (0 : ℝ) < (piUp : ℝ) := by simp only [piUp]; norm_num
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hG : Real.Gamma (2 * (τ : ℝ) + 1) = ((2 * τ).factorial : ℝ) := by
    rw [show 2 * (τ : ℝ) + 1 = ((2 * τ : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have hp : 2 * (τ : ℝ) = ((2 * τ : ℕ) : ℝ) := by push_cast; ring
  have hf : (0 : ℝ) < ((2 * τ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi := pi_lt_piUp
  have hed := eLo_lt
  have hb : (2 * (τ : ℝ) / Real.exp 1) ≤ 2 * (τ : ℝ) / (eLo : ℝ) := by gcongr
  have hb0 : 0 ≤ 2 * (τ : ℝ) / Real.exp 1 := by positivity
  unfold sdEps epsUp
  rw [hG]
  nth_rewrite 2 [hp]
  rw [Real.rpow_natCast]
  push_cast
  gcongr

/-- **`classicalOk` is sound.** -/
theorem cohConstC_le_of_ok {n τ J : ℕ} {δ c : ℚ} (hδ : 0 ≤ δ)
    (h : classicalOk n τ J δ c = true) : cohConstC n τ δ ≤ c := by
  simp only [classicalOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hr⟩ := h
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hpi := piLo_lt
  have hpi0 : (0 : ℝ) < (piLo : ℝ) := by simp only [piLo]; norm_num
  have hG : Real.Gamma (2 * (τ : ℝ) + 1) = ((2 * τ).factorial : ℝ) := by
    rw [show 2 * (τ : ℝ) + 1 = ((2 * τ : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have hA := shellConst_le_shellUp τ J
  have hA0 := shellConst_pos (τ := τ) (Nat.cast_nonneg τ)
  have hε := sdEps_le_epsUp τ hδ
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hε0 : 0 ≤ sdEps (τ : ℝ) (4 * Real.pi * δ) := sdEps_nonneg (Nat.cast_nonneg τ) (by positivity)
  have hf : (0 : ℝ) < ((2 * τ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hrad : (2 : ℝ) ^ n * (shellConst τ * Real.Gamma (2 * (τ : ℝ) + 1) *
      (1 + sdEps τ (4 * Real.pi * δ))) ≤ (radUp n τ J δ : ℝ) := by
    have hS0 : (0 : ℝ) ≤ (shellUp τ J : ℝ) := hA0.le.trans hA
    have hE0 : (0 : ℝ) ≤ 1 + (epsUp τ δ : ℝ) := by linarith
    rw [hG]
    simp only [radUp]
    push_cast
    gcongr
  have hr' : (radUp n τ J δ : ℝ) ≤ ((c : ℝ) * (2 * piLo) * (4 * piLo) ^ τ) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hr
    push_cast at this
    exact this
  have hq : 0 ≤ (c : ℝ) * (2 * piLo) * (4 * piLo) ^ τ := by positivity
  have hs : Real.sqrt ((2 : ℝ) ^ n * (shellConst τ * Real.Gamma (2 * (τ : ℝ) + 1) *
      (1 + sdEps τ (4 * Real.pi * δ)))) ≤ (c : ℝ) * (2 * piLo) * (4 * piLo) ^ τ :=
    (Real.sqrt_le_sqrt (hrad.trans hr')).trans_eq (Real.sqrt_sq hq)
  have h1 : (2 * Real.pi)⁻¹ ≤ (2 * (piLo : ℝ))⁻¹ := by gcongr
  have h2 : (4 * Real.pi) ^ (-(τ : ℝ)) ≤ ((4 * (piLo : ℝ)) ^ τ)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    gcongr
  unfold cohConstC
  calc (2 * Real.pi)⁻¹ * _ * (4 * Real.pi) ^ (-(τ : ℝ))
      ≤ (2 * (piLo : ℝ))⁻¹ * ((c : ℝ) * (2 * piLo) * (4 * piLo) ^ τ) *
          ((4 * (piLo : ℝ)) ^ τ)⁻¹ := by
        gcongr
    _ = c := by field_simp

/-- Rational majorants of the classical constants at the schedule are certificates on the
Diophantine set. -/
theorem NumA.cert_of_le {N : NumA} (hN : N.Wf) (hρ1 : N.ρ ≤ 1) {γ : ℝ} (hγ : 0 < γ)
    (hc : ∀ s < N.kp, cohConstC N.n N.τ (N.δ s) ≤ N.c s)
    (hcb : ∀ s < N.kp, cohConstC N.n N.τ (N.r s) ≤ N.cbar s)
    (ht : cohConstC N.n N.τ (N.δ N.kp) ≤ N.ctail) :
    N.Cert γ {ω | IsDiophantine γ N.τ ω} where
  stage := fun s hs =>
    sdConst_mono hγ (sdConst_classical (by have := hN.two_le; omega) hN.τ_ge hγ (hN.δ_pos s)
      (hN.δ_le s)) (hc s hs)
  bar := fun s hs =>
    sdConst_mono hγ (sdConst_classical (by have := hN.two_le; omega) hN.τ_ge hγ (hN.r_pos s)
      ((hN.r_le s).trans hρ1)) (hcb s hs)
  tail := fun δ hδ hle => by
    have h1 := sdConst_classical (n := N.n) (by have := hN.two_le; omega) hN.τ_ge hγ hδ
      (hle.trans (hN.δ_le _))
    exact sdConst_mono hγ h1 ((cohConstC_mono hN.τ_ge hδ.le hle).trans ht)

end KAM.CertificateSharp.V2

end
