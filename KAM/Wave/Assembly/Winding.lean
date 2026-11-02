/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.Ext

/-!
# W8: winding of the tangential phases (blueprint `bpW:w8:winding`)

Blueprint label `bpW:w8:winding` (milestone W8).

If `a(t) e^{-2πi φ(t)} = a'(t) e^{-2πi φ'(t)}` for all `t`, with `a, a' > 0` and `φ, φ'`
continuous, and `φ(t) - t ν₀`, `φ'(t) - t ν₀'` bounded, then `ν₀ = ν₀'`
(`KAM.Wave.winding_rate_eq`).
-/

public section

namespace KAM.Wave

/-- **Winding** (blueprint `bpW:w8:winding`). -/
theorem winding_rate_eq {a a' φ φ' : ℝ → ℝ} {ν₀ ν₀' : ℝ}
    (_ha : Continuous a) (_ha' : Continuous a') (hφ : Continuous φ) (hφ' : Continuous φ')
    (hapos : ∀ t, 0 < a t) (ha'pos : ∀ t, 0 < a' t)
    (hb : ∃ B, ∀ t, |φ t - t * ν₀| ≤ B) (hb' : ∃ B, ∀ t, |φ' t - t * ν₀'| ≤ B)
    (heq : ∀ t, (a t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * φ t)) =
      (a' t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * φ' t))) :
    ν₀ = ν₀' := by
  -- Step `stepW:w8:w-mod`: moduli, then `φ - φ' ∈ ℤ`
  have hnorm : ∀ x : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * x))‖ = 1 := fun x => by
    have : -(2 * Real.pi * Complex.I * x) = ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this]; exact (w8ext_norm_exp_I _).1
  have haa : ∀ t, a t = a' t := fun t => by
    have := congrArg norm (heq t)
    rwa [norm_mul, norm_mul, hnorm, hnorm, mul_one, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hapos t),
      abs_of_pos (ha'pos t)] at this
  have hint : ∀ t, ∃ k : ℤ, φ t - φ' t = k := fun t => by
    have h1 := heq t
    rw [haa t] at h1
    have hne : (a' t : ℂ) ≠ 0 := by exact_mod_cast (ha'pos t).ne'
    have h2 := mul_left_cancel₀ hne h1
    have h3 : Complex.exp (-(2 * Real.pi * Complex.I * (φ t - φ' t))) = 1 := by
      have : -(2 * Real.pi * Complex.I * ((φ t : ℂ) - φ' t)) =
          -(2 * Real.pi * Complex.I * φ t) - -(2 * Real.pi * Complex.I * φ' t) := by ring
      rw [this, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := (w8ext_exp_eq_one_iff _).1 h3
    refine ⟨-n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h4 : ((φ t - φ' t : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ hpi
      push_cast
      linear_combination (-1 : ℂ) * hn
    exact_mod_cast h4
  -- Step `stepW:w8:w-const`: `φ - φ'` is a constant `c`
  have hconst : ∀ t, φ t - φ' t = φ 0 - φ' 0 := fun t =>
    w8ext_const_of_intValued (hφ.sub hφ') hint t 0
  -- Step `stepW:w8:w-rate`: `t (ν₀ - ν₀')` is bounded
  obtain ⟨B, hB⟩ := hb
  obtain ⟨B', hB'⟩ := hb'
  have hbound : ∀ t : ℝ, |t * (ν₀ - ν₀')| ≤ |φ 0 - φ' 0| + B + B' := fun t => by
    have e : t * (ν₀ - ν₀') = (φ 0 - φ' 0) - (φ t - t * ν₀) + (φ' t - t * ν₀') := by
      linarith [hconst t]
    rw [e]
    calc |(φ 0 - φ' 0) - (φ t - t * ν₀) + (φ' t - t * ν₀')|
        ≤ |(φ 0 - φ' 0) - (φ t - t * ν₀)| + |φ' t - t * ν₀'| := abs_add_le _ _
      _ ≤ |φ 0 - φ' 0| + |φ t - t * ν₀| + |φ' t - t * ν₀'| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith [hB t, hB' t]
  exact sub_eq_zero.1 (w8ext_eq_zero_of_bounded_mul hbound)

end KAM.Wave

end
