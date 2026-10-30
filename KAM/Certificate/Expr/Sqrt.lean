/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The total square root `sqrtE`

`sqrtE z` is the semantics of the `sqrt` node of the Hamiltonian expression language. It is total,
like Lean's `0⁻¹ = 0`: `0` on the closed nonpositive real axis and the principal root `z ^ (1/2)`
elsewhere. It maps reals to reals (`sqrtE_ofReal`), agrees with `exp (log z / 2)` on the slit
plane, where it is holomorphic (`contDiffAt_sqrtE`, `hasDerivAt_sqrtE`), squares back to its
argument there (`sqrtE_sq`) and always has nonnegative real part (`sqrtE_re_nonneg`).

The ball rule `sqrtE_ball` (`|z - s²| ≤ r < s²`, `s > 0` give `0 < re z` and `|√z - s| ≤ r/s`) and
the model rule `sqrtE_model_error` (positive real anchor `s` and margin `d < s`) are the scalar
facts behind the ball step and the composition witness of `sqrt`.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open Complex

/-- The total square root: `0` on the nonpositive real axis, the principal root elsewhere. -/
def sqrtE (z : ℂ) : ℂ := if z.im = 0 ∧ z.re ≤ 0 then 0 else z ^ (1 / 2 : ℂ)

theorem sqrtE_eq_exp {z : ℂ} (hz : z ∈ slitPlane) : sqrtE z = exp (log z * (1 / 2)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hc : ¬ (z.im = 0 ∧ z.re ≤ 0) := by
    rw [mem_slitPlane_iff] at hz
    rintro ⟨h1, h2⟩
    rcases hz with h | h
    · linarith
    · exact h h1
  simp only [sqrtE, hc, ↓reduceIte]
  exact cpow_def_of_ne_zero hz0 _

theorem sqrtE_eventuallyEq {z : ℂ} (hz : z ∈ slitPlane) :
    sqrtE =ᶠ[nhds z] fun w => exp (log w * (1 / 2)) :=
  Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun _ hw => sqrtE_eq_exp hw

theorem contDiffAt_sqrtE {z : ℂ} (hz : z ∈ slitPlane) {m : WithTop ℕ∞} :
    ContDiffAt ℂ m sqrtE z :=
  (((contDiffAt_log hz).mul contDiffAt_const).cexp).congr_of_eventuallyEq
    (sqrtE_eventuallyEq hz)

/-- Holomorphy on the slit plane, in particular on the certified region `0 < re`. -/
theorem differentiableAt_sqrtE {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ sqrtE z :=
  (contDiffAt_sqrtE hz (m := 1)).differentiableAt (by simp)

theorem sqrtE_sq {z : ℂ} (hz : z ∈ slitPlane) : sqrtE z ^ 2 = z := by
  rw [sqrtE_eq_exp hz, sq, ← exp_add, ← mul_add]
  norm_num
  exact exp_log (slitPlane_ne_zero hz)

theorem sqrtE_ne_zero {z : ℂ} (hz : z ∈ slitPlane) : sqrtE z ≠ 0 := by
  intro h
  have := sqrtE_sq hz
  rw [h] at this
  exact slitPlane_ne_zero hz (by simpa using this.symm)

theorem sqrtE_re_nonneg (z : ℂ) : 0 ≤ (sqrtE z).re := by
  by_cases hc : z.im = 0 ∧ z.re ≤ 0
  · simp [sqrtE, hc]
  · have hz : z ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      by_contra h
      push Not at h
      exact hc ⟨h.2, h.1⟩
    rw [sqrtE_eq_exp hz, exp_re]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
    · have h1 := neg_pi_lt_arg z
      have : (log z * (1 / 2)).im = z.arg / 2 := by
        simp [log_im]
        ring
      rw [this]
      linarith
    · have h1 := arg_le_pi z
      have : (log z * (1 / 2)).im = z.arg / 2 := by
        simp [log_im]
        ring
      rw [this]
      linarith

theorem mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl hz)

/-- New proof case of `HamExpr.exists_real_eval`: reals go to reals. -/
theorem sqrtE_ofReal (x : ℝ) : ∃ r : ℝ, sqrtE (x : ℂ) = (r : ℂ) := by
  by_cases hx : x ≤ 0
  · exact ⟨0, by simp [sqrtE, hx]⟩
  · push Not at hx
    refine ⟨x ^ (1 / 2 : ℝ), ?_⟩
    have hc : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by simp [hx.not_ge]
    simp only [sqrtE, hc, ↓reduceIte]
    rw [ofReal_cpow hx.le]
    norm_num

/-- Derivative on the slit plane: `(√z)' = 1/(2√z)`. -/
theorem hasDerivAt_sqrtE_of_mem {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt sqrtE (1 / (2 * sqrtE z)) z := by
  have h1 : HasDerivAt (fun w => exp (log w * (1 / 2))) (exp (log z * (1 / 2)) * (z⁻¹ * (1 / 2)))
      z := ((hasStrictDerivAt_log hz).hasDerivAt.mul_const (1 / 2)).cexp
  have h2 := h1.congr_of_eventuallyEq (sqrtE_eventuallyEq hz)
  convert h2 using 1
  have hs := sqrtE_sq hz
  have hs0 := sqrtE_ne_zero hz
  rw [← sqrtE_eq_exp hz]
  have hz' : z⁻¹ = (sqrtE z)⁻¹ ^ 2 := by rw [inv_pow, hs]
  rw [hz']
  field_simp

/-- Derivative rule used by the differentiation layer (`d√f = f′/(2√f)`). -/
theorem hasDerivAt_sqrtE {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt sqrtE (1 / (2 * sqrtE z)) z :=
  hasDerivAt_sqrtE_of_mem (mem_slitPlane_of_re_pos hz)

/-- Pointwise model rule with a positive real anchor: `‖W − s‖ ≤ d < s` puts `W` in the right
half-plane, so `|√f + W| ≥ s − d` without knowing the error. -/
theorem sqrtE_model_error {f W : ℂ} {s d ε : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (hds : d < s)
    (hf : 0 < f.re) (hW : ‖W - (s : ℂ)‖ ≤ d) (hres : ‖f - W ^ 2‖ ≤ ε) :
    ‖sqrtE f - W‖ ≤ ε / (s - d) := by
  have _ := hs
  have _ := hd
  have hfs := mem_slitPlane_of_re_pos hf
  have hWre : s - d ≤ W.re := by
    have h := (abs_re_le_norm (W - (s : ℂ))).trans hW
    rw [sub_re, ofReal_re] at h
    linarith [neg_abs_le (W.re - s)]
  have hsum : s - d ≤ ‖sqrtE f + W‖ := by
    have h := re_le_norm (sqrtE f + W)
    rw [add_re] at h
    linarith [sqrtE_re_nonneg f]
  have hpos : 0 < s - d := by linarith
  have e : (sqrtE f - W) * (sqrtE f + W) = f - W ^ 2 := by
    have := sqrtE_sq hfs
    linear_combination this
  rw [le_div_iff₀ hpos]
  calc ‖sqrtE f - W‖ * (s - d) ≤ ‖sqrtE f - W‖ * ‖sqrtE f + W‖ :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖f - W ^ 2‖ := by rw [← norm_mul, e]
    _ ≤ ε := hres

/-- Ball rule (before outward rounding): `|z − s²| ≤ r < s²`, `s > 0` ⇒ `0 < re z` and
`|√z − s| ≤ r/s`. The `SlpOp.sqrt` ball step checks `r < s²`. -/
theorem sqrtE_ball {z : ℂ} {s r : ℝ} (hs : 0 < s) (hr : r < s ^ 2)
    (h : ‖z - (s : ℂ) ^ 2‖ ≤ r) : 0 < z.re ∧ ‖sqrtE z - s‖ ≤ r / s := by
  have hre : 0 < z.re := by
    have h1 := (abs_re_le_norm (z - (s : ℂ) ^ 2)).trans h
    have e : (z - (s : ℂ) ^ 2).re = z.re - s ^ 2 := by
      rw [sub_re, ← ofReal_pow, ofReal_re]
    rw [e] at h1
    linarith [neg_abs_le (z.re - s ^ 2)]
  refine ⟨hre, ?_⟩
  have := sqrtE_model_error (W := (s : ℂ)) (d := 0) hs le_rfl hs hre (by simp) h
  simpa using this

end KAM.Certificate

end
