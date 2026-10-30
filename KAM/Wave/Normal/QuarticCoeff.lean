/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Wave.Defs.SineMode
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The quartic coefficients `g_{ijkl}` (blueprint `bpW:w0n:quartic-coeff`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`KAM.Wave.quarticCoeff i j k l = ∫₀^π φ_i φ_j φ_k φ_l dx` for the frozen `sineMode`. We prove the
closed form of blueprint-W Lemma `bpW:w0n:quartic-coeff` (the Iverson-bracket formula, symmetry,
the selection rule, the diagonal values and the signed form `bpW:w0n:g-signed`).

The product `φ_i φ_j φ_k φ_l` is `(2/π)² · (1/8) ·` a signed sum of eight cosines of integer
multiples of `x`; the cosine integral over `[0, π]` is `π` for the zero frequency and `0`
otherwise.
-/

@[expose] public noncomputable section

open intervalIntegral Real

namespace KAM.Wave

/-- The quartic coefficient `g_{ijkl} = ∫₀^π φ_i φ_j φ_k φ_l dx` (blueprint
    `bpW:w0n:quartic-coeff`). -/
def quarticCoeff (i j k l : ℕ+) : ℝ :=
  ∫ x in (0 : ℝ)..π, sineMode i x * sineMode j x * sineMode k x * sineMode l x

/-- `∫₀^π cos (n x) dx` is `π` for `n = 0` and `0` otherwise. -/
theorem integral_cos_int_mul (n : ℤ) :
    ∫ x in (0 : ℝ)..π, Real.cos ((n : ℝ) * x) = if n = 0 then π else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn']
    simp [hn, Real.sin_int_mul_pi]

/-- Product-to-sum for four sines. -/
theorem sin_mul_four (a b c d : ℝ) :
    Real.sin a * Real.sin b * Real.sin c * Real.sin d =
      (1 / 8) * (Real.cos ((a - b) - (c - d)) + Real.cos ((a - b) + (c - d))
        - Real.cos ((a - b) - (c + d)) - Real.cos ((a - b) + (c + d))
        - Real.cos ((a + b) - (c - d)) - Real.cos ((a + b) + (c - d))
        + Real.cos ((a + b) - (c + d)) + Real.cos ((a + b) + (c + d))) := by
  simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
  ring

/-- The integrand of `quarticCoeff` as a signed sum of eight cosines of integer frequencies. -/
theorem sineMode_mul_four (i j k l : ℕ+) (x : ℝ) :
    sineMode i x * sineMode j x * sineMode k x * sineMode l x =
      (1 / (2 * π ^ 2)) *
        (Real.cos ((((i : ℕ) : ℤ) - j - (k - l) : ℤ) * x)
          + Real.cos ((((i : ℕ) : ℤ) - j + (k - l) : ℤ) * x)
          - Real.cos ((((i : ℕ) : ℤ) - j - (k + l) : ℤ) * x)
          - Real.cos ((((i : ℕ) : ℤ) - j + (k + l) : ℤ) * x)
          - Real.cos ((((i : ℕ) : ℤ) + j - (k - l) : ℤ) * x)
          - Real.cos ((((i : ℕ) : ℤ) + j + (k - l) : ℤ) * x)
          + Real.cos ((((i : ℕ) : ℤ) + j - (k + l) : ℤ) * x)
          + Real.cos ((((i : ℕ) : ℤ) + j + (k + l) : ℤ) * x)) := by
  have hs : Real.sqrt (2 / π) ^ 4 = (2 / π) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  have h4 : sineMode i x * sineMode j x * sineMode k x * sineMode l x
      = Real.sqrt (2 / π) ^ 4 * (Real.sin (i * x) * Real.sin (j * x) * Real.sin (k * x)
        * Real.sin (l * x)) := by
    unfold sineMode; ring
  rw [h4, hs, sin_mul_four]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  push_cast
  ring_nf

/-- Closed form of the quartic coefficients (blueprint `bpW:w0n:quartic-coeff`): the Iverson
bracket formula. -/
theorem quarticCoeff_eq (i j k l : ℕ+) :
    quarticCoeff i j k l = (1 / (2 * π)) *
      ((if (i : ℕ) + l = j + k then 1 else 0) + (if (i : ℕ) + k = j + l then 1 else 0)
        + (if (i : ℕ) + j = k + l then 1 else 0)
        - (if (i : ℕ) = j + k + l then 1 else 0) - (if (j : ℕ) = i + k + l then 1 else 0)
        - (if (k : ℕ) = i + j + l then 1 else 0) - (if (l : ℕ) = i + j + k then 1 else 0)) := by
  unfold quarticCoeff
  simp_rw [sineMode_mul_four]
  have hc : ∀ n : ℤ, IntervalIntegrable (fun x : ℝ => Real.cos ((n : ℝ) * x)) MeasureTheory.volume
      0 π := fun n => (by fun_prop : Continuous fun x : ℝ => Real.cos ((n : ℝ) *
          x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul]
  have e : ∀ f : ℤ → ℝ → ℝ, (∀ n, IntervalIntegrable (f n) MeasureTheory.volume 0 π) →
      ∀ n1 n2 n3 n4 n5 n6 n7 n8 : ℤ,
      ∫ x in (0 : ℝ)..π, (f n1 x + f n2 x - f n3 x - f n4 x - f n5 x - f n6 x + f n7 x + f n8 x)
        = (∫ x in (0 : ℝ)..π, f n1 x) + (∫ x in (0 : ℝ)..π, f n2 x)
          - (∫ x in (0 : ℝ)..π, f n3 x) - (∫ x in (0 : ℝ)..π, f n4 x)
          - (∫ x in (0 : ℝ)..π, f n5 x) - (∫ x in (0 : ℝ)..π, f n6 x)
          + (∫ x in (0 : ℝ)..π, f n7 x) + (∫ x in (0 : ℝ)..π, f n8 x) := by
    intro f hf n1 n2 n3 n4 n5 n6 n7 n8
    have h := hf
    have i2 := (h n1).add (h n2)
    have i3 := i2.sub (h n3)
    have i4 := i3.sub (h n4)
    have i5 := i4.sub (h n5)
    have i6 := i5.sub (h n6)
    have i7 := i6.add (h n7)
    rw [intervalIntegral.integral_add i7 (h n8), intervalIntegral.integral_add i6 (h n7),
      intervalIntegral.integral_sub i5 (h n6), intervalIntegral.integral_sub i4 (h n5),
      intervalIntegral.integral_sub i3 (h n4), intervalIntegral.integral_sub i2 (h n3),
      intervalIntegral.integral_add (h n1) (h n2)]
  rw [e (fun n x => Real.cos ((n : ℝ) * x)) hc]
  simp only [integral_cos_int_mul]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hz : ∀ (a b : ℕ), (((a : ℤ) - b = 0)) ↔ a = b := fun a b => by omega
  have h1 : ((i : ℕ) : ℤ) - j - (k - l) = 0 ↔ (i : ℕ) + l = j + k := by omega
  have h2 : ((i : ℕ) : ℤ) - j + (k - l) = 0 ↔ (i : ℕ) + k = j + l := by omega
  have h3 : ((i : ℕ) : ℤ) - j - (k + l) = 0 ↔ (i : ℕ) = j + k + l := by omega
  have h4 : ((i : ℕ) : ℤ) - j + (k + l) = 0 ↔ (j : ℕ) = i + k + l := by omega
  have h5 : ((i : ℕ) : ℤ) + j - (k - l) = 0 ↔ (k : ℕ) = i + j + l := by omega
  have h6 : ((i : ℕ) : ℤ) + j + (k - l) = 0 ↔ (l : ℕ) = i + j + k := by omega
  have h7 : ((i : ℕ) : ℤ) + j - (k + l) = 0 ↔ (i : ℕ) + j = k + l := by omega
  have h8 : ¬ (((i : ℕ) : ℤ) + j + (k + l) = 0) := by
    have := i.pos; have := j.pos; omega
  have hite : ∀ (p : Prop) [Decidable p], (if p then π else 0) = π * (if p then (1 : ℝ) else 0) :=
    fun p _ => by split_ifs <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false, hite]
  field_simp
  ring

/-- The sign `s(ε) = (-1)^(1 + #{t : ε_t = -1})` of blueprint `bpW:w0n:g-signed`, for
`ε ∈ {±1}³` coded by `Bool` (`true ↦ +1`, `false ↦ -1`). -/
def signedSign (ε : Bool × Bool × Bool) : ℤ :=
  (-1) ^ (1 + ((if ε.1 then 0 else 1) + (if ε.2.1 then 0 else 1) + (if ε.2.2 then 0 else 1)))

/-- The value `ε_t ∈ {+1, -1}` of a `Bool`. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

/-- Signed form of the quartic coefficients (blueprint `bpW:w0n:g-signed`). -/
theorem quarticCoeff_signed (i j k l : ℕ+) :
    quarticCoeff i j k l = (1 / (2 * π)) * ∑ ε : Bool × Bool × Bool,
      (signedSign ε : ℝ) *
        (if ((l : ℕ) : ℤ) = boolSign ε.1 * (i : ℕ) + boolSign ε.2.1 * (j : ℕ)
          + boolSign ε.2.2 * (k : ℕ) then 1 else 0) := by
  rw [quarticCoeff_eq]
  simp [Fintype.sum_prod_type, signedSign, boolSign]
  have p1 := i.pos
  have p2 := j.pos
  have p3 := k.pos
  have p4 := l.pos
  have c1 : (((l : ℕ) : ℤ) = (i : ℕ) + (j : ℕ) + (k : ℕ)) ↔ (l : ℕ) = i + j + k := by omega
  have c2 : (((l : ℕ) : ℤ) = (i : ℕ) + (j : ℕ) + -(k : ℕ)) ↔ (i : ℕ) + j = k + l := by omega
  have c3 : (((l : ℕ) : ℤ) = (i : ℕ) + -(j : ℕ) + (k : ℕ)) ↔ (i : ℕ) + k = j + l := by omega
  have c4 : (((l : ℕ) : ℤ) = (i : ℕ) + -(j : ℕ) + -(k : ℕ)) ↔ (i : ℕ) = j + k + l := by omega
  have c5 : (((l : ℕ) : ℤ) = -(i : ℕ) + (j : ℕ) + (k : ℕ)) ↔ (i : ℕ) + l = j + k := by omega
  have c6 : (((l : ℕ) : ℤ) = -(i : ℕ) + (j : ℕ) + -(k : ℕ)) ↔ (j : ℕ) = i + k + l := by omega
  have c7 : (((l : ℕ) : ℤ) = -(i : ℕ) + -(j : ℕ) + (k : ℕ)) ↔ (k : ℕ) = i + j + l := by omega
  have c8 : ¬ (((l : ℕ) : ℤ) = -(i : ℕ) + -(j : ℕ) + -(k : ℕ)) := by omega
  have hneg : ∀ (p : Prop) [Decidable p], (if p then (-1 : ℝ) else 0) = -(if p then 1 else 0) :=
    fun p _ => by split_ifs <;> simp
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, ite_false, hneg, show ((-1 : ℝ)) ^ 3 = -1 by norm_num,
    show ((-1 : ℝ)) ^ 4 = 1 by norm_num]
  ring

/-- The selection rule of `quarticCoeff`: a signed relation `±i ± j ± k ± l = 0` (the seven
relations of the closed form). -/
def QuarticSel (a b c d : ℕ) : Prop :=
  a + d = b + c ∨ a + c = b + d ∨ a + b = c + d ∨
    a = b + c + d ∨ b = a + c + d ∨ c = a + b + d ∨ d = a + b + c

/-- `g_{ijkl} = 0` unless the selection rule holds (blueprint `bpW:w0n:quartic-coeff`). -/
theorem quarticCoeff_eq_zero_of_not_sel (i j k l : ℕ+) (h : ¬ QuarticSel i j k l) :
    quarticCoeff i j k l = 0 := by
  unfold QuarticSel at h
  push Not at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [quarticCoeff_eq]
  simp [h1, h2, h3, h4, h5, h6, h7]

/-- `g_{ijkl} ≠ 0` forces the selection rule. -/
theorem quarticSel_of_quarticCoeff_ne_zero (i j k l : ℕ+) (h : quarticCoeff i j k l ≠ 0) :
    QuarticSel i j k l :=
  by_contra fun hn => h (quarticCoeff_eq_zero_of_not_sel i j k l hn)

/-- Symmetry of `g` under all permutations of the four indices (blueprint
`bpW:w0n:quartic-coeff`). -/
theorem quarticCoeff_perm (v : Fin 4 → ℕ+) (σ : Equiv.Perm (Fin 4)) :
    quarticCoeff (v (σ 0)) (v (σ 1)) (v (σ 2)) (v (σ 3)) = quarticCoeff (v 0) (v 1) (v 2) (v 3) :=
        by
  have key : ∀ (w : Fin 4 → ℕ+) (x : ℝ), sineMode (w 0) x * sineMode (w 1) x * sineMode (w 2) x
      * sineMode (w 3) x = ∏ t, sineMode (w t) x := fun w x => by
    simp [Fin.prod_univ_four]
  unfold quarticCoeff
  congr 1
  ext x
  rw [key (fun t => v (σ t)) x, key v x]
  exact Equiv.prod_comp σ (fun t => sineMode (v t) x)

/-- `g_{iiii} = 3 / (2π)`. -/
theorem quarticCoeff_diag (i : ℕ+) : quarticCoeff i i i i = 3 / (2 * π) := by
  have := i.pos
  rw [quarticCoeff_eq]
  have h1 : ¬ (i : ℕ) = i + i + i := by omega
  simp only [h1, ite_false, ite_true]
  ring

/-- `g_{iijj} = 1 / π` for `i ≠ j`. -/
theorem quarticCoeff_diag_pair (i j : ℕ+) (hij : i ≠ j) : quarticCoeff i i j j = 1 / π := by
  have hne : (i : ℕ) ≠ j := fun h => hij (PNat.coe_injective h)
  have p1 := i.pos
  have p2 := j.pos
  rw [quarticCoeff_eq]
  have h1 : ¬ (i : ℕ) + i = j + j := by omega
  have h2 : ¬ (i : ℕ) = i + j + j := by omega
  have h5 : ¬ (j : ℕ) = i + i + j := by omega
  simp only [h1, h2, h5, ite_false, ite_true]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  norm_num

/-- `|g_{ijkl}| ≤ (1/2π) · #{ε : l = ε₁ i + ε₂ j + ε₃ k}` (blueprint `bpW:w0n:g-signed`). -/
theorem abs_quarticCoeff_le (i j k l : ℕ+) :
    |quarticCoeff i j k l| ≤ (1 / (2 * π)) * ∑ ε : Bool × Bool × Bool,
      (if ((l : ℕ) : ℤ) = boolSign ε.1 * (i : ℕ) + boolSign ε.2.1 * (j : ℕ)
          + boolSign ε.2.2 * (k : ℕ) then (1 : ℝ) else 0) := by
  rw [quarticCoeff_signed, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ε _ => ?_)
  rw [abs_mul]
  have : |(signedSign ε : ℝ)| = 1 := by
    unfold signedSign
    push_cast
    rw [abs_pow]; simp
  rw [this, one_mul]
  split_ifs <;> simp

end KAM.Wave

end
