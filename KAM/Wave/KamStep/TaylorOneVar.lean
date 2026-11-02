/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Taylor series in one complex variable, Banach values (external fact `bpW:w5:ext-taylor`)

If `g : ℂ → E` is holomorphic on `|t| < ρ` with `‖g t‖ ≤ B` there, then the Taylor coefficients
`g_k = (k!)⁻¹ g^{(k)}(0)` satisfy `‖g_k‖ ≤ B ρ^{-k}` (`norm_taylorCoeff_le`) and for `|t| ≤ 1 < ρ`
`‖g t - ∑_{k ≤ 2} g_k t^k‖ ≤ B ρ^{-3}/(1 - ρ^{-1})` (`norm_taylor_remainder_le`).
-/

@[expose] public section

open Metric Set

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Taylor coefficient `g_k = (k!)⁻¹ g^{(k)}(0)`. -/
noncomputable def taylorCoeff (g : ℂ → E) (k : ℕ) : E := ((k.factorial : ℂ)⁻¹) • iteratedDeriv k g 0

/-- **Coefficient bound** `‖g_k‖ ≤ B ρ^{-k}`. -/
theorem norm_taylorCoeff_le {g : ℂ → E} {ρ B : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (ball 0 ρ)) (hB : ∀ t ∈ ball 0 ρ, ‖g t‖ ≤ B) (k : ℕ) :
    ‖taylorCoeff g k‖ ≤ B / ρ ^ k := by
  have key : ∀ r : ℝ, 0 < r → r < ρ → ‖taylorCoeff g k‖ ≤ B / r ^ k := by
    intro r hr hrρ
    have hcl : closedBall (0 : ℂ) r ⊆ ball 0 ρ := closedBall_subset_ball hrρ
    have hd : DiffContOnCl ℂ g (ball 0 r) := by
      refine DifferentiableOn.diffContOnCl (hg.mono ?_)
      rw [closure_ball _ hr.ne']; exact hcl
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hd
      (fun z hz => hB z (hcl (sphere_subset_closedBall hz)))
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    unfold taylorCoeff
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    calc (k.factorial : ℝ)⁻¹ * ‖iteratedDeriv k g 0‖
        ≤ (k.factorial : ℝ)⁻¹ * (k.factorial * B / r ^ k) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = B / r ^ k := by field_simp
  by_contra hlt
  push Not at hlt
  have hρk : 0 < ρ ^ k := pow_pos hρ k
  -- continuity of `r ↦ B / r^k` at `ρ`
  have hcont : ContinuousAt (fun r : ℝ => B / r ^ k) ρ :=
    continuousAt_const.div (continuousAt_id.pow k) hρk.ne'
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont (‖taylorCoeff g k‖ - B / ρ ^ k)
    (by linarith)
  set r := max (ρ - δ / 2) (ρ / 2) with hr
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hrρ : r < ρ := max_lt (by linarith) (by linarith)
  have hdist : dist r ρ < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have : ρ - δ / 2 ≤ r := le_max_left _ _
    linarith
  have h1 := hδ' hdist
  have h2 := key r hr0 hrρ
  rw [Real.dist_eq] at h1
  have := (abs_lt.mp h1).2
  linarith

/-- **Remainder bound**: for `|t| ≤ 1 < ρ`,
`‖g t - ∑_{k ≤ 2} t^k g_k‖ ≤ B ρ^{-3}/(1 - ρ^{-1})`. -/
theorem norm_taylor_remainder_le {g : ℂ → E} {ρ B : ℝ} (hρ : 1 < ρ)
    (hg : DifferentiableOn ℂ g (ball 0 ρ)) (hB : ∀ t ∈ ball 0 ρ, ‖g t‖ ≤ B) {t : ℂ}
    (ht : ‖t‖ ≤ 1) :
    ‖g t - ∑ k ∈ Finset.range 3, t ^ k • taylorCoeff g k‖ ≤ B / ρ ^ 3 / (1 - 1 / ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have htρ : t ∈ ball (0 : ℂ) ρ := by rw [mem_ball_zero_iff]; linarith
  have hB0 : 0 ≤ B := by
    have := norm_taylorCoeff_le hρ0 hg hB 0
    simp only [pow_zero, div_one] at this
    exact (norm_nonneg _).trans this
  have hS : HasSum (fun n : ℕ => t ^ n • taylorCoeff g n) (g t) := by
    have := Complex.hasSum_taylorSeries_on_ball hg htρ
    convert this using 2 with n
    simp only [taylorCoeff, sub_zero]
    exact smul_comm _ _ _
  have h3 := (hasSum_nat_add_iff' 3).mpr hS
  have hgeo : HasSum (fun n : ℕ => B / ρ ^ 3 * (1 / ρ) ^ n) (B / ρ ^ 3 * (1 - 1 / ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by rw [div_lt_one hρ0]; exact hρ)).mul_left _
  have := h3.norm_le_of_bounded hgeo (fun n => by
    have hc := norm_taylorCoeff_le hρ0 hg hB (n + 3)
    rw [norm_smul, norm_pow]
    have h1 : ‖t‖ ^ (n + 3) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht
    calc ‖t‖ ^ (n + 3) * ‖taylorCoeff g (n + 3)‖ ≤ 1 * (B / ρ ^ (n + 3)) :=
          mul_le_mul h1 hc (norm_nonneg _) zero_le_one
      _ = B / ρ ^ 3 * (1 / ρ) ^ n := by
          rw [one_mul, pow_add, one_div, inv_pow]; field_simp)
  simpa [div_eq_mul_inv] using this

end KAM.Wave
