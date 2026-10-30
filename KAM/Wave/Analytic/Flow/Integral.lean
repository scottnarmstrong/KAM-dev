/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral estimates over `[0, t]`, for both signs of `t`

Blueprint-W `bpW:w1:flow`, step `stepW:w1:wavePicard` (package W1-ANALYTIC). This is source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

If `‖f σ‖ ≤ g |σ|` on the integration interval and `G' = g`, then `‖∫₀ᵗ f‖ ≤ G |t| - G 0`
(`KAM.Wave.norm_integral_le_primitive`); with `g = c xᵐ` and `g = L e^{L x}` this gives the two
estimates used for the Picard iterates.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Interval

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `‖∫₀ᵗ f‖ ≤ G |t| - G 0` when `‖f σ‖ ≤ g |σ|` and `G' = g` on `[0, ∞)`. -/
theorem norm_integral_le_primitive {f : ℝ → E} {g G : ℝ → ℝ} {t : ℝ} (hg : Continuous g)
    (hG : ∀ x, 0 ≤ x → HasDerivAt G (g x) x) (hf : ∀ σ ∈ Ι 0 t, ‖f σ‖ ≤ g |σ|) :
    ‖∫ σ in (0 : ℝ)..t, f σ‖ ≤ G |t| - G 0 := by
  have hint : ∀ b : ℝ, 0 ≤ b → ∫ x in (0 : ℝ)..b, g x = G b - G 0 := fun b hb =>
    integral_eq_sub_of_hasDerivAt (fun x hx => hG x (by
      rw [uIcc_of_le hb] at hx; exact hx.1)) (hg.intervalIntegrable 0 b)
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, ← hint t ht]
    refine norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall fun σ hσ => ?_)
      (hg.intervalIntegrable 0 t)
    have hσ0 : 0 ≤ σ := hσ.1.le
    have := hf σ (by rw [uIoc_of_le ht]; exact hσ)
    simpa [abs_of_nonneg hσ0] using this
  · have hneg : ∫ σ in (0 : ℝ)..t, f σ = -∫ σ in (0 : ℝ)..-t, f (-σ) := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -t) (fun x => f x)
      rw [neg_neg, neg_zero] at this
      rw [this, intervalIntegral.integral_symm]
    rw [hneg, norm_neg, abs_of_nonpos ht, ← hint (-t) (by linarith)]
    have hae : ∀ᵐ σ : ℝ, σ ∉ ({-t} : Set ℝ) := (Set.countable_singleton (-t)).ae_notMem _
    refine norm_integral_le_of_norm_le (by linarith) (hae.mono fun σ hσ' hσ => ?_)
      (hg.intervalIntegrable 0 (-t))
    have hσ0 : 0 ≤ σ := hσ.1.le
    have hne : σ ≠ -t := hσ'
    have := hf (-σ) (by
      rw [uIoc_of_ge ht]
      exact ⟨by have := lt_of_le_of_ne hσ.2 hne; linarith, by linarith [hσ.1]⟩)
    simpa [abs_of_nonneg hσ0] using this

/-- Polynomial bound: `‖f σ‖ ≤ c |σ|ᵐ` gives `‖∫₀ᵗ f‖ ≤ c |t|ᵐ⁺¹ / (m + 1)`. -/
theorem norm_integral_le_pow {f : ℝ → E} {c : ℝ} {m : ℕ} {t : ℝ}
    (hf : ∀ σ ∈ Ι 0 t, ‖f σ‖ ≤ c * |σ| ^ m) :
    ‖∫ σ in (0 : ℝ)..t, f σ‖ ≤ c * |t| ^ (m + 1) / (m + 1) := by
  have := norm_integral_le_primitive (f := f) (g := fun x => c * |x| ^ m)
    (G := fun x => c * x ^ (m + 1) / (m + 1)) (t := t) (by fun_prop) (fun x hx => ?_)
    (by simpa using hf)
  · simpa using this
  · have h := ((hasDerivAt_pow (m + 1) x).const_mul c).div_const ((m : ℝ) + 1)
    convert h using 1
    rw [abs_of_nonneg hx]
    push_cast
    field_simp

/-- Exponential bound: `‖f σ‖ ≤ L e^{L |σ|}` gives `‖∫₀ᵗ f‖ ≤ e^{L |t|} - 1`. -/
theorem norm_integral_le_exp {f : ℝ → E} {L t : ℝ}
    (hf : ∀ σ ∈ Ι 0 t, ‖f σ‖ ≤ L * Real.exp (L * |σ|)) :
    ‖∫ σ in (0 : ℝ)..t, f σ‖ ≤ Real.exp (L * |t|) - 1 := by
  have := norm_integral_le_primitive (f := f) (g := fun x => L * Real.exp (L * x))
    (G := fun x => Real.exp (L * x)) (t := t) (by fun_prop) (fun x _ => ?_) hf
  · simpa using this
  · have h := ((hasDerivAt_id x).const_mul L).exp
    simpa [mul_comm] using h

end KAM.Wave
