/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageDom

/-!
# Slow averaging: the objects `Z`, `h₀`, `f₂` and the sup bound of `f₂` (P11A-P7b, `as-osc`)

`P11SlowPolarOut` packages the output of `p11_slow_polar`; `p11SlowZ`, `p11SlowH0`, `p11SlowF2`
are the explicit `Ẑ = 𝒜R₄ + 𝒜ḡ`, `h₀ = h + ε (C + Σ Ω ρ̃/2π + Ẑ)` and
`f₂ = ε (G ∘ Π - (C + Σ Ω ρ̃/2π + Ẑ)) + f₁ ∘ Π`.  The box `p11SlowBox` is
`D(J₀, s₁/4) × D(2πε, πε)`.  `p11_slow_f2_sup`: `sup |f₂| ≤ c ε^{5/2} (log 1/ε)^{2τ+1}` on the
strip `|Im ·| < σ/6`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section F2

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- The action box `D(J₀, s₁/4) × D(2πε, πε)`. -/
def p11SlowBox (C : P11SecularData n) (eps : ℝ) : Set (P11CVec (n + n)) :=
  p11Box (Fin.append (KAM.realInclusion n C.J0) (fun _ : Fin n => (2 * Real.pi * eps : ℂ)))
    (p11s1 C eps / 4) (Real.pi * eps)

/-- Output of `p11_slow_polar` (polar averages of `R₄` and `ḡ`). -/
def P11SlowPolarOut (C : P11SecularData n) (Fast : P11FastData n) (eps : ℝ)
    (AR AB : P11CVec n × P11CVec n → ℂ) : Prop :=
  let S := ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
    ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4)
  DifferentiableOn ℂ AR S ∧ DifferentiableOn ℂ AB S ∧
  (∀ z ∈ S, ‖AR z‖ ≤ 2 ^ (2 * n) * (C.MF / 16) *
    (4 * ‖z.2‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2) ∧
  (∀ z ∈ S, ‖AB z‖ ≤ 2 ^ (2 * n) * p11eta1 C eps) ∧
  (∀ z ∈ S, (∀ i, 0 < (z.2 i).re) →
    AR z = p11PolarAverage (p11R4 C) z ∧ AB z = p11PolarAverage (p11Gbar C Fast) z)

theorem p11_slow_polar_out (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1)) :
    ∃ AR AB : P11CVec n × P11CVec n → ℂ, P11SlowPolarOut C Fast eps AR AB := by
  obtain ⟨AR, AB, h1, h2, h3, h4, h5⟩ := p11_slow_polar hC Fast hF heps hεM
  exact ⟨AR, AB, h1, h2, h3, h4, h5⟩

/-- `Ẑ(I) = 𝒜R₄ + 𝒜ḡ` on the full action vector. -/
def p11SlowZ (AR AB : P11CVec n × P11CVec n → ℂ) (I : P11CVec (n + n)) : ℂ :=
  AR (p11SlowJ I, p11SlowR I) + AB (p11SlowJ I, p11SlowR I)

/-- `h₀ = h + ε (C + Σ Ω ρ̃/2π + Ẑ)`. -/
def p11SlowH0 (C : P11SecularData n) (eps : ℝ) (Z : P11CVec (n + n) → ℂ)
    (I : P11CVec (n + n)) : ℂ :=
  C.h (fun i : Fin n => I (Fin.castAdd n i)) + eps * (p11SlowSec C I + Z I)

/-- `f₂ = ε (G ∘ Π - (C + Σ Ω ρ̃/2π + Ẑ)) + f₁ ∘ Π`. -/
def p11SlowF2 (C : P11SecularData n) (Fast : P11FastData n) (eps : ℝ)
    (Z : P11CVec (n + n) → ℂ) (z : P11Phase (n + n)) : ℂ :=
  eps * (Fast.G (p11SlowJ z.2, p11PolPt z) - (p11SlowSec C z.2 + Z z.2)) +
    Fast.f1 (p11PolarC z)

/-- Data of a point of the box: `J` within `s₁/4`, `ρ̃` with positive real part, `‖ρ̃‖ < 3πε`. -/
theorem p11SlowBox_mem {eps : ℝ} (heps : 0 < eps) (hs : 0 < p11s1 C eps) {I : P11CVec (n + n)}
    (hI : I ∈ p11SlowBox C eps) :
    ‖p11SlowJ I - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 ∧
      ‖p11SlowR I‖ < 3 * Real.pi * eps ∧ ∀ i, 0 < (p11SlowR I i).re := by
  obtain ⟨hJ, hR⟩ := hI
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, fun i => ?_⟩
  · refine (pi_norm_lt_iff (by linarith)).2 fun i => ?_
    simpa [p11SlowJ, Fin.append_left] using hJ i
  · refine (pi_norm_lt_iff (by positivity)).2 fun i => ?_
    have h := hR i
    simp only [Fin.append_right] at h
    have : ‖I (Fin.natAdd n i)‖ ≤ ‖I (Fin.natAdd n i) - (2 * Real.pi * eps : ℂ)‖ +
        ‖(2 * Real.pi * eps : ℂ)‖ := norm_le_norm_sub_add _ _
    have h2 : ‖(2 * Real.pi * eps : ℂ)‖ = 2 * Real.pi * eps := by
      rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp only [p11SlowR]
    linarith
  · have h := hR i
    simp only [Fin.append_right] at h
    have h1 := Complex.abs_re_le_norm (I (Fin.natAdd n i) - (2 * Real.pi * eps : ℂ))
    have h3 : (I (Fin.natAdd n i) - (2 * Real.pi * eps : ℂ)).re =
        (I (Fin.natAdd n i)).re - 2 * Real.pi * eps := by
      simp
    rw [h3] at h1
    have := (abs_lt.1 (h1.trans_lt h)).1
    simp only [p11SlowR]
    nlinarith

end F2

end KAM.Planetary

end
