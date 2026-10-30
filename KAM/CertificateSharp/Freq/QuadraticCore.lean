/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.IsDiophantine
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The norm tail of the exact quadratic Diophantine constant

For `ω = (α, 1)` with `α` a root of `A x² + B x + C` and conjugate `α'`, the integer
`N(k) = C k₁² - B k₁k₂ + A k₂²` equals `A (k₁α + k₂)(k₁α' + k₂)`. It is nonzero for `k ≠ 0` when
`α, α'` are irrational. `quad_tail_core` is the real-number half of the exact-infimum
certificate (design `CERTIFIER-SHARPNESS` §2.5): for `|k₁| ≥ K₀` and a constant `γ` with
`γ (1 + A γ) ≤ K₀² (1 + a₀ - A γ D)` (`a₀ ≤ |α|`, `D ≥ |α - α'|`) one has
`γ / (|k₁| + |k₂|) ≤ |k₁ α + k₂|`. The finite part `|k₁| < K₀` is `QuadraticExact`.
-/

@[expose] public section

namespace KAM.CertificateSharp

/-- The norm identity `A (k₁α + k₂)(k₁α' + k₂) = C k₁² - B k₁k₂ + A k₂²`. -/
theorem quad_norm_eq {A B C : ℤ} {α α' : ℝ} (hsum : (A : ℝ) * (α + α') = -B)
    (hprod : (A : ℝ) * (α * α') = C) (k1 k2 : ℤ) :
    ((C * k1 ^ 2 - B * k1 * k2 + A * k2 ^ 2 : ℤ) : ℝ) =
      A * ((k1 * α + k2) * (k1 * α' + k2)) := by
  push_cast
  linear_combination (-(k1 : ℝ) ^ 2) * hprod + (-(k1 : ℝ) * k2) * hsum

/-- Real-number tail: `γ / (|k₁| + |k₂|) ≤ |k₁α + k₂|` once `|k₁| ≥ K₀`. -/
theorem quad_tail_core {A B C : ℤ} {α α' D a0 γ K0 : ℝ} (hA : 0 < (A : ℝ))
    (hsum : (A : ℝ) * (α + α') = -B) (hprod : (A : ℝ) * (α * α') = C)
    (hαi : Irrational α) (hα'i : Irrational α') (hD : |α - α'| ≤ D) (ha0 : a0 ≤ |α|)
    (hγ : 0 < γ) (hK : 1 ≤ K0) (hpos : 0 < 1 + a0 - A * γ * D)
    (htail : γ * (1 + A * γ) ≤ K0 ^ 2 * (1 + a0 - A * γ * D)) (k1 k2 : ℤ)
    (hk1 : K0 ≤ |(k1 : ℝ)|) :
    γ / (|(k1 : ℝ)| + |(k2 : ℝ)|) ≤ |k1 * α + k2| := by
  set m : ℝ := |(k1 : ℝ)| with hm
  set x : ℝ := |k1 * α + k2| with hx
  have hm1 : 1 ≤ m := hK.trans hk1
  have hm0 : 0 < m := by linarith
  have hx0 : 0 ≤ x := abs_nonneg _
  have hk2 : 0 ≤ |(k2 : ℝ)| := abs_nonneg _
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hs0 : 0 < m + |(k2 : ℝ)| := by linarith
  by_contra hcon
  push Not at hcon
  have hxs : x * (m + |(k2 : ℝ)|) < γ := by
    rw [lt_div_iff₀ hs0] at hcon
    exact hcon
  have hxm : x * m < γ := by nlinarith
  have hk1ne : (k1 : ℝ) ≠ 0 := by
    intro h
    rw [hm, h, abs_zero] at hm0
    exact lt_irrefl _ hm0
  -- the norm is a nonzero integer
  have hNeq := quad_norm_eq hsum hprod k1 k2
  have hN0 : (C * k1 ^ 2 - B * k1 * k2 + A * k2 ^ 2 : ℤ) ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hNeq
    have h1 : (k1 * α + k2) * (k1 * α' + k2) = 0 := by
      have := hNeq.symm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hA.ne'
      · exact h
    rcases mul_eq_zero.mp h1 with h | h
    · apply hαi
      refine ⟨(-k2 / k1 : ℚ), ?_⟩
      push_cast
      field_simp
      linarith
    · apply hα'i
      refine ⟨(-k2 / k1 : ℚ), ?_⟩
      push_cast
      field_simp
      linarith
  have hN1 : (1 : ℝ) ≤ |((C * k1 ^ 2 - B * k1 * k2 + A * k2 ^ 2 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hN0
  set y : ℝ := |k1 * α' + k2| with hy
  have hxy : 1 ≤ A * (x * y) := by
    rw [hNeq, abs_mul, abs_mul, abs_of_pos hA] at hN1
    exact hN1
  have hyle : y ≤ x + m * D := by
    have e : k1 * α' + k2 = (k1 * α + k2) - k1 * (α - α') := by ring
    rw [hy, e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have : |(k1 : ℝ)| * |α - α'| ≤ m * D := mul_le_mul_of_nonneg_left hD (abs_nonneg _)
    linarith
  have h1 : 1 ≤ A * (x * (x + m * D)) := by
    refine hxy.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyle hx0) hA.le
  -- m ≤ P x
  have hP : m ≤ A * (γ + m ^ 2 * D) * x := by
    have h2 : m ≤ m * (A * (x * (x + m * D))) := by nlinarith
    have h3 : m * (A * (x * (x + m * D))) = A * x * (x * m + m ^ 2 * D) := by ring
    have h4 : A * x * (x * m + m ^ 2 * D) ≤ A * x * (γ + m ^ 2 * D) := by
      have : 0 ≤ A * x := mul_nonneg hA.le hx0
      exact mul_le_mul_of_nonneg_left (by linarith) this
    nlinarith
  -- |k₂| ≥ m a₀ - x
  have hk2lb : m * a0 - x ≤ |(k2 : ℝ)| := by
    have e : (k2 : ℝ) = (k1 * α + k2) - k1 * α := by ring
    have h5 : |(k1 : ℝ) * α| - |k1 * α + k2| ≤ |(k2 : ℝ)| := by
      calc |(k1 : ℝ) * α| - |k1 * α + k2|
          ≤ |(k1 : ℝ) * α - (k1 * α + k2)| := abs_sub_abs_le_abs_sub _ _
        _ = |(k2 : ℝ)| := by rw [show (k1 : ℝ) * α - (k1 * α + k2) = -(k2 : ℝ) by ring, abs_neg]
    rw [abs_mul] at h5
    have : m * a0 ≤ |(k1 : ℝ)| * |α| := mul_le_mul_of_nonneg_left ha0 hm0.le
    linarith
  set u : ℝ := m ^ 2 with hu
  have hu1 : K0 ^ 2 ≤ u := by
    rw [hu]; exact pow_le_pow_left₀ (by linarith) hk1 2
  have hPpos : 0 < A * (γ + u * D) := by positivity
  have hpos' : 0 < γ + u * D := by positivity
  have hs0' : 0 ≤ u * (1 + a0) - γ := by
    have h6 : γ * (1 + A * γ) ≤ u * (1 + a0 - A * γ * D) :=
      htail.trans (mul_le_mul_of_nonneg_right hu1 hpos.le)
    have h7 : u * (1 + a0 - A * γ * D) ≤ u * (1 + a0) := by
      have : 0 ≤ u * (A * γ * D) := by positivity
      nlinarith
    have : γ ≤ γ * (1 + A * γ) := by nlinarith [mul_pos hA hγ, mul_pos (mul_pos hA hγ) hγ]
    linarith
  -- s x ≥ (u(1+a0) - γ)/P ≥ γ
  have hsx : (m * (1 + a0) - γ / m) * x ≤ (m + |(k2 : ℝ)|) * x := by
    have : m * (1 + a0) - γ / m ≤ m + |(k2 : ℝ)| := by
      have hxg : x ≤ γ / m := by rw [le_div_iff₀ hm0]; linarith
      linarith
    exact mul_le_mul_of_nonneg_right this hx0
  have hlow : (u * (1 + a0) - γ) * x ≥ (u * (1 + a0) - γ) * (m / (A * (γ + u * D))) := by
    refine mul_le_mul_of_nonneg_left ?_ hs0'
    rw [div_le_iff₀ hPpos]
    linarith
  have hid : (m * (1 + a0) - γ / m) = (u * (1 + a0) - γ) / m := by
    rw [hu]; field_simp
  have hfin : γ ≤ (u * (1 + a0) - γ) / (A * (γ + u * D)) := by
    rw [le_div_iff₀ hPpos]
    have h6 : γ * (1 + A * γ) ≤ u * (1 + a0 - A * γ * D) :=
      htail.trans (mul_le_mul_of_nonneg_right hu1 hpos.le)
    linarith
  have hkey : (u * (1 + a0) - γ) / (A * (γ + u * D)) ≤ (m * (1 + a0) - γ / m) * x := by
    have e1 : (u * (1 + a0) - γ) / (A * (γ + u * D)) =
        (u * (1 + a0) - γ) * (m / (A * (γ + u * D))) / m := by
      field_simp
    have e2 : (m * (1 + a0) - γ / m) * x = (u * (1 + a0) - γ) * x / m := by
      rw [hid]; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hlow hm0.le
  linarith

end KAM.CertificateSharp
