/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.Compose
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Bihomogeneous polynomials in polar variables (T2-CONF, N5a)

With `w_k = √I_k e^{iθ_k}` (`polarW`), a term `c w^b w̄^{b'}` is
`c Π_k √I_k^{b_k + b'_k} e^{i Σ_k (b_k - b'_k) θ_k}`, so the real part of a polynomial with integer
coefficients in `(s w, s w̄)` (`s` real) is a cosine sum (`re_bevalAt_polarW`). For charge-zero
terms (`|b| = |b'|`) the angle depends on `θ` only through `φ = (θ₀ - θ₂, θ₁ - θ₂)`
(`polarAngle_of_charge`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Complex

/-- `w_k = √I_k e^{iθ_k}`. -/
def polarW (act θ : Fin 3 → ℝ) : Fin 3 → ℂ := fun k => (√(act k) : ℂ) * exp (θ k * I)

/-- The amplitude `Π_k √I_k^{b_k + b'_k}` of the term `w^b w̄^{b'}`. -/
def polarAmp (act : Fin 3 → ℝ) (b : Mon × Mon) : ℝ :=
  √(act 0) ^ (b.1.1 + b.2.1) * √(act 1) ^ (b.1.2.1 + b.2.2.1) * √(act 2) ^ (b.1.2.2 + b.2.2.2)

/-- The angle `Σ_k (b_k - b'_k) θ_k` of the term `w^b w̄^{b'}`. -/
def polarAngle (θ : Fin 3 → ℝ) (b : Mon × Mon) : ℝ :=
  ((b.1.1 : ℝ) - b.2.1) * θ 0 + ((b.1.2.1 : ℝ) - b.2.2.1) * θ 1 + ((b.1.2.2 : ℝ) - b.2.2.2) * θ 2

private theorem factor_polar (r t : ℝ) (m m' : ℕ) :
    ((r : ℂ) * exp (t * I)) ^ m * (star ((r : ℂ) * exp (t * I))) ^ m' =
      ((r ^ (m + m') : ℝ) : ℂ) * exp ((((m : ℝ) - m') * t : ℝ) * I) := by
  have hs : star ((r : ℂ) * exp (t * I)) = (r : ℂ) * exp ((-t : ℝ) * I) := by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  rw [hs, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have he : exp ((((m : ℝ) - m') * t : ℝ) * I) =
      exp (m * (t * I)) * exp (m' * ((-t : ℝ) * I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ring

/-- **One term in polar variables.** -/
theorem mon_polarW_mul_star (act θ : Fin 3 → ℝ) (b : Mon × Mon) :
    mon b.1 (polarW act θ) * mon b.2 (fun k => star (polarW act θ k)) =
      (polarAmp act b : ℂ) * exp ((polarAngle θ b : ℝ) * I) := by
  have h0 := factor_polar (√(act 0)) (θ 0) b.1.1 b.2.1
  have h1 := factor_polar (√(act 1)) (θ 1) b.1.2.1 b.2.2.1
  have h2 := factor_polar (√(act 2)) (θ 2) b.1.2.2 b.2.2.2
  have he : exp ((polarAngle θ b : ℝ) * I) =
      exp (((((b.1.1 : ℝ) - b.2.1) * θ 0 : ℝ)) * I) *
        exp (((((b.1.2.1 : ℝ) - b.2.2.1) * θ 1 : ℝ)) * I) *
        exp (((((b.1.2.2 : ℝ) - b.2.2.2) * θ 2 : ℝ)) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [polarAngle]
    push_cast
    ring
  have hl : mon b.1 (polarW act θ) * mon b.2 (fun k => star (polarW act θ k)) =
      (((√(act 0) : ℂ) * exp (θ 0 * I)) ^ b.1.1 * (star ((√(act 0) : ℂ) * exp (θ 0 * I))) ^ b.2.1) *
      (((√(act 1) : ℂ) * exp (θ 1 * I)) ^ b.1.2.1 *
        (star ((√(act 1) : ℂ) * exp (θ 1 * I))) ^ b.2.2.1) *
      (((√(act 2) : ℂ) * exp (θ 2 * I)) ^ b.1.2.2 *
        (star ((√(act 2) : ℂ) * exp (θ 2 * I))) ^ b.2.2.2) := by
    simp only [mon, polarW]
    ring
  rw [hl, h0, h1, h2, he, polarAmp]
  push_cast
  ring

/-- `mon b (s w) = s^{|b|} mon b w`. -/
theorem mon_smul {R : Type*} [CommRing R] (s : R) (b : Mon) (w : Fin 3 → R) :
    mon b (fun k => s * w k) = s ^ b.deg * mon b w := by
  simp only [mon, Mon.deg, mul_pow, pow_add]
  ring

/-- **The real part in polar variables.** For integer coefficients and a real scale `s`,
`Re Σ c (s w)^b (s w̄)^{b'}
  = Σ c s^{|b| + |b'|} Π_k √I_k^{b_k + b'_k} cos (Σ_k (b_k - b'_k) θ_k)`. -/
theorem re_bevalAt_polarW (p : List ((Mon × Mon) × ℤ)) (s : ℝ) (act θ : Fin 3 → ℝ) :
    (bevalAt p (fun k => (s : ℂ) * polarW act θ k) (fun k => (s : ℂ) * star (polarW act θ k))).re =
      (p.map fun e => (e.2 : ℝ) * s ^ (Mon.deg e.1.1 + Mon.deg e.1.2) * polarAmp act e.1 *
        Real.cos (polarAngle θ e.1)).sum := by
  induction p with
  | nil => simp
  | cons e p ih =>
    rw [bevalAt_cons, Complex.add_re, ih, List.map_cons, List.sum_cons, mon_smul, mon_smul]
    congr 1
    have : (e.2 : ℂ) * ((s : ℂ) ^ Mon.deg e.1.1 * mon e.1.1 (polarW act θ) *
        ((s : ℂ) ^ Mon.deg e.1.2 * mon e.1.2 (fun k => star (polarW act θ k)))) =
        (((e.2 : ℝ) * s ^ (Mon.deg e.1.1 + Mon.deg e.1.2) * polarAmp act e.1 : ℝ) : ℂ) *
          exp ((polarAngle θ e.1 : ℝ) * I) := by
      have hm := mon_polarW_mul_star act θ e.1
      calc (e.2 : ℂ) * ((s : ℂ) ^ Mon.deg e.1.1 * mon e.1.1 (polarW act θ) *
            ((s : ℂ) ^ Mon.deg e.1.2 * mon e.1.2 (fun k => star (polarW act θ k))))
          = (e.2 : ℂ) * (s : ℂ) ^ (Mon.deg e.1.1 + Mon.deg e.1.2) *
            (mon e.1.1 (polarW act θ) * mon e.1.2 (fun k => star (polarW act θ k))) := by
            rw [pow_add]; ring
        _ = _ := by rw [hm]; push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Charge zero**: if `|b| = |b'|`, the angle is `(b₀ - b'₀) φ₀ + (b₁ - b'₁) φ₁` with
`φ = (θ₀ - θ₂, θ₁ - θ₂)`. -/
theorem polarAngle_of_charge (θ : Fin 3 → ℝ) (b : Mon × Mon) (h : Mon.deg b.1 = Mon.deg b.2) :
    polarAngle θ b =
      ((b.1.1 : ℝ) - b.2.1) * (θ 0 - θ 2) + ((b.1.2.1 : ℝ) - b.2.2.1) * (θ 1 - θ 2) := by
  simp only [Mon.deg] at h
  have h' : ((b.1.1 : ℝ) + b.1.2.1 + b.1.2.2) = (b.2.1 : ℝ) + b.2.2.1 + b.2.2.2 := by
    exact_mod_cast h
  simp only [polarAngle]
  linear_combination θ 2 * h'

end KAM.EffectiveStability.Tube

end
