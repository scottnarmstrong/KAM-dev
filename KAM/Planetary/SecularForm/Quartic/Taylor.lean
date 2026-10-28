/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Secular form: reading a Taylor coefficient off an `O(s⁶)` expansion

Blueprint P, Part 8, `stepP:p8:q4-b`: an analytic function of one variable that agrees with an even
quartic polynomial up to `O(s⁶)` has fourth derivative `24 C` at the origin.
-/

@[expose] public noncomputable section
open Set Filter Real Function
open scoped Topology
namespace KAM.Planetary

namespace SecularForm

/-- A function analytic at `0` that is `O(|s|⁶)` near `0` has vanishing derivatives of order `< 6`. -/
theorem iteratedDeriv_eq_zero_of_isBigO {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) {K r : ℝ}
    (hr : 0 < r) (h : ∀ s, |s| < r → |g s| ≤ K * |s| ^ 6) :
    ∀ k < 6, iteratedDeriv k g 0 = 0 := by
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg]
  by_contra hlt
  push Not at hlt
  have hne : analyticOrderAt g 0 ≠ ⊤ := fun h' => by simp [h'] at hlt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hm] at hlt
  have hm6 : m < 6 := by exact_mod_cast hlt
  obtain ⟨u, hu, hu0, hev⟩ := (hg.analyticOrderAt_eq_natCast.1 hm.symm)
  have hunz : 0 < |u 0| := abs_pos.2 hu0
  have hcont : ContinuousAt u 0 := hu.continuousAt
  have h1 : ∀ᶠ s in 𝓝 (0:ℝ), |u 0| / 2 < |u s| := by
    have := hcont.abs.eventually (lt_mem_nhds (show |u 0| / 2 < |u 0| by linarith))
    exact this
  have h2 : ∀ᶠ s in 𝓝 (0:ℝ), |s| < r := by
    have : ∀ᶠ s in 𝓝 (0:ℝ), s ∈ Metric.ball (0:ℝ) r := Metric.ball_mem_nhds _ hr
    filter_upwards [this] with s hs
    simpa using hs
  have h3 : ∀ᶠ s in 𝓝 (0:ℝ), |s| < min 1 (|u 0| / 2 / (|K| + 1)) := by
    have : ∀ᶠ s in 𝓝 (0:ℝ), s ∈ Metric.ball (0:ℝ) (min 1 (|u 0| / 2 / (|K| + 1))) :=
      Metric.ball_mem_nhds _ (lt_min one_pos (by positivity))
    filter_upwards [this] with s hs
    simpa using hs
  have hall : ∀ᶠ s in 𝓝[≠] (0:ℝ), (|u 0| / 2 < |u s| ∧ |s| < r ∧
      g s = (s - 0) ^ m • u s ∧ |s| < min 1 (|u 0| / 2 / (|K| + 1))) ∧ s ≠ 0 :=
    ((h1.and (h2.and (hev.and h3))).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, ⟨hs1, hs2, hs3, hs4⟩, hs0⟩ := hall.exists
  have hspos : 0 < |s| := abs_pos.2 hs0
  have hs1' : |s| < 1 := lt_of_lt_of_le hs4 (min_le_left _ _)
  have hs2' : |s| < |u 0| / 2 / (|K| + 1) := lt_of_lt_of_le hs4 (min_le_right _ _)
  have hg := h s hs2
  rw [hs3, sub_zero, smul_eq_mul, abs_mul, abs_pow] at hg
  have e : ∃ e : ℕ, 6 = m + e ∧ e ≠ 0 := ⟨6 - m, by omega, by omega⟩
  obtain ⟨e, he, he0⟩ := e
  have hse : |s| ^ e ≤ |s| := pow_le_of_le_one hspos.le hs1'.le he0
  have hpm : 0 < |s| ^ m := pow_pos hspos m
  have h6 : |s| ^ 6 = |s| ^ m * |s| ^ e := by rw [he, pow_add]
  have hK : K * |s| ^ 6 ≤ (|K| + 1) * (|s| ^ m * |s|) := by
    rw [h6]
    have : K * (|s| ^ m * |s| ^ e) ≤ |K| * (|s| ^ m * |s| ^ e) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h' : |K| * (|s| ^ m * |s| ^ e) ≤ (|K| + 1) * (|s| ^ m * |s|) := by
      have : |s| ^ m * |s| ^ e ≤ |s| ^ m * |s| := mul_le_mul_of_nonneg_left hse hpm.le
      nlinarith [abs_nonneg K]
    linarith
  have hlow : |s| ^ m * (|u 0| / 2) < |s| ^ m * |u s| := mul_lt_mul_of_pos_left hs1 hpm
  have : |u 0| / 2 < (|K| + 1) * |s| := by
    have h5 : |s| ^ m * (|u 0| / 2) < (|s| ^ m) * ((|K| + 1) * |s|) := by nlinarith
    exact lt_of_mul_lt_mul_left h5 hpm.le
  have : |s| * (|K| + 1) < |u 0| / 2 := by
    rwa [lt_div_iff₀ (by positivity)] at hs2'
  nlinarith

/-- The fourth derivative of an analytic function that is `P(s) + O(s⁶)` with `P` an even
quartic polynomial. -/
theorem iteratedDeriv_four_of_expansion {ψ : ℝ → ℝ} (hψ : AnalyticAt ℝ ψ 0) {A B C K r : ℝ}
    (hr : 0 < r) (h : ∀ s, |s| < r → |ψ s - (A + B * s ^ 2 + C * s ^ 4)| ≤ K * |s| ^ 6) :
    iteratedDeriv 4 ψ 0 = 24 * C := by
  have hP : AnalyticAt ℝ (fun s : ℝ => A + B * s ^ 2 + C * s ^ 4) 0 := by fun_prop
  have hz := iteratedDeriv_eq_zero_of_isBigO (hψ.fun_sub hP) hr h 4 (by norm_num)
  rw [iteratedDeriv_fun_sub hψ.contDiffAt hP.contDiffAt] at hz
  have hP4 : iteratedDeriv 4 (fun s : ℝ => A + B * s ^ 2 + C * s ^ 4) 0 = 24 * C := by
    rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
      iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
    rw [iteratedDeriv_const_mul (c := C) (by fun_prop)]
    rw [iteratedDeriv_const_mul (c := B) (by fun_prop)]
    have h0 : iteratedDeriv 4 (fun _ : ℝ => A) 0 = 0 := by
      simpa using iteratedDeriv_const (n := 4) (c := A) (x := (0:ℝ))
    rw [h0]; simp; ring
  linarith

end SecularForm
end KAM.Planetary
end
