/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.EquationComplex
public import KAM.Planetary.Preparation.SlowAverageZ

/-!
# Slow averaging: the oscillation estimate (P11A-P7b, graph step `as-osc`)

`G ∘ Π - Ĝ₀ = (R₄ + ḡ) ∘ Π - (𝒜R₄ + 𝒜ḡ)` on the polar region, bounded by
`c (ε² + η₁ √ε)`: `p11_slow_osc_pointwise`.  Here `Π = p11PolPt z` is the polar point of
`z = (ζ, I)`, and `p11SlowSec` is `C + Σ Ω_i ρ_i / 2π`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Osc

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Action block of the slow (`J`) variables of a full action vector. -/
def p11SlowJ (I : P11CVec (n + n)) : P11CVec n := fun i => I (Fin.castAdd n i)

/-- Action block of the oscillator (`ρ̃`) variables of a full action vector. -/
def p11SlowR (I : P11CVec (n + n)) : P11CVec n := fun i => I (Fin.natAdd n i)

/-- The polar point `Π(ζ, ρ̃) = (√(ρ̃/π) sin 2πζ, √(ρ̃/π) cos 2πζ)` of a point of the full chart. -/
def p11PolPt (z : P11Phase (n + n)) : P11Phase n :=
  ((fun i => (p11PolarC z).1 (Fin.natAdd n i)), fun i => (p11PolarC z).2 (Fin.natAdd n i))

/-- The secular part `C(J) + Σ Ω_i(J) ρ̃_i / 2π` of the averaged Hamiltonian. -/
def p11SlowSec (C : P11SecularData n) (I : P11CVec (n + n)) : ℂ :=
  C.C (fun i : Fin n => I (Fin.castAdd n i)) +
    ∑ i : Fin n, C.Omega (fun j : Fin n => I (Fin.castAdd n j)) i / (2 * Real.pi) *
      I (Fin.natAdd n i)

theorem p11PolPt_fst (z : P11Phase (n + n)) (i : Fin n) :
    (p11PolPt z).1 i = Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi) *
      Complex.sin (2 * Real.pi * z.1 (Fin.natAdd n i)) := by
  simp [p11PolPt, p11PolarC]

theorem p11PolPt_snd (z : P11Phase (n + n)) (i : Fin n) :
    (p11PolPt z).2 i = Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi) *
      Complex.cos (2 * Real.pi * z.1 (Fin.natAdd n i)) := by
  simp [p11PolPt, p11PolarC]

/-- On the strip `|Im ζ_i| ≤ 1/8` the polar point has norm `≤ 2 √(‖ρ̃‖/π)`. -/
theorem p11PolPt_norm_le (z : P11Phase (n + n))
    (hz : ∀ i : Fin n, |(z.1 (Fin.natAdd n i)).im| ≤ 1 / 8) :
    ‖p11PolPt z‖ ≤ 2 * Real.sqrt (‖p11SlowR z.2‖ / Real.pi) := by
  have hcosh : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
    linarith
  have hs0 : 0 ≤ Real.sqrt (‖p11SlowR z.2‖ / Real.pi) := Real.sqrt_nonneg _
  have key : ∀ (f : ℂ → ℂ) (i : Fin n), (∀ w : ℂ, |w.im| ≤ 1 → ‖f w‖ ≤ Real.cosh 1) →
      ‖Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi) * f (2 * Real.pi * z.1 (Fin.natAdd n i))‖ ≤
        2 * Real.sqrt (‖p11SlowR z.2‖ / Real.pi) := by
    intro f i hf
    rw [norm_mul]
    have h1 : ‖Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi)‖ ≤
        Real.sqrt (‖p11SlowR z.2‖ / Real.pi) := by
      have := p11_rad_norm_le (p11SlowR z.2)
      exact (norm_le_pi_norm (p11Rad (p11SlowR z.2)) i).trans this
    have him : |(2 * Real.pi * z.1 (Fin.natAdd n i)).im| ≤ 1 := by
      have : (2 * Real.pi * z.1 (Fin.natAdd n i)).im = 2 * Real.pi * (z.1 (Fin.natAdd n i)).im := by
        simp [Complex.mul_im]
      rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have := hz i
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    calc _ ≤ Real.sqrt (‖p11SlowR z.2‖ / Real.pi) * Real.cosh 1 :=
          mul_le_mul h1 ((hf _ him)) (norm_nonneg _) hs0
      _ ≤ _ := by nlinarith
  rw [Prod.norm_def, max_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [p11PolPt_fst]
    exact key Complex.sin i fun w hw => KAM.Kepler.EqC.norm_sin_le hw
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [p11PolPt_snd]
    exact key Complex.cos i fun w hw => KAM.Kepler.EqC.norm_cos_le hw

/-- `G ∘ Π = C + Σ Ω ρ̃/2π + R₄ ∘ Π + ḡ ∘ Π` (exact; `x² + y² = ρ̃/π` on polar points). -/
theorem p11_slow_G_polar (C : P11SecularData n) (Fast : P11FastData n) (z : P11Phase (n + n)) :
    Fast.G (p11SlowJ z.2, p11PolPt z) = p11SlowSec C z.2 +
      p11R4 C (p11SlowJ z.2, p11PolPt z) + p11Gbar C Fast (p11SlowJ z.2, p11PolPt z) := by
  rw [p11G_decomp C Fast (p11SlowJ z.2, p11PolPt z)]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hterm : ∀ i : Fin n, C.Omega (p11SlowJ z.2) i *
      (((p11PolPt z).1 i ^ 2 + (p11PolPt z).2 i ^ 2) / 2) =
      C.Omega (fun j : Fin n => z.2 (Fin.castAdd n j)) i / (2 * Real.pi) *
        z.2 (Fin.natAdd n i) := by
    intro i
    rw [p11PolPt_fst, p11PolPt_snd]
    have h1 := p11_sqrt_sq (z.2 (Fin.natAdd n i) / Real.pi)
    have h2 := Complex.sin_sq_add_cos_sq (2 * Real.pi * z.1 (Fin.natAdd n i))
    have : (Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi) *
          Complex.sin (2 * Real.pi * z.1 (Fin.natAdd n i))) ^ 2 +
        (Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi) *
          Complex.cos (2 * Real.pi * z.1 (Fin.natAdd n i))) ^ 2 =
        z.2 (Fin.natAdd n i) / Real.pi := by
      calc _ = Complex.sqrt (z.2 (Fin.natAdd n i) / Real.pi) ^ 2 *
            (Complex.sin (2 * Real.pi * z.1 (Fin.natAdd n i)) ^ 2 +
              Complex.cos (2 * Real.pi * z.1 (Fin.natAdd n i)) ^ 2) := by ring
        _ = _ := by rw [h2, h1, mul_one]
    rw [this]
    change C.Omega (fun j : Fin n => z.2 (Fin.castAdd n j)) i *
      (z.2 (Fin.natAdd n i) / Real.pi / 2) = _
    field_simp
  have hJ : p11SlowJ z.2 = fun j : Fin n => z.2 (Fin.castAdd n j) := rfl
  simp only [p11SlowSec, hterm]
  rw [hJ]

end Osc

end KAM.Planetary

end
