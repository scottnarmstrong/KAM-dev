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

/-- The constant of the `f₂` bound. -/
def p11SlowC0 (C : P11SecularData n) (c1 : ℝ) : ℝ :=
  256 * C.MF / C.rz ^ 4 + 2 ^ (2 * n) * 9 * C.MF / (C.rz / 2) ^ 4 + 12 / (C.rz / 2) * c1 +
    C.MF ^ 3

/-- Real bookkeeping of the `f₂` bound: `ε (K₀ ε² + K₁ η √ε) + M ε³ ≤ (K₀ + K₁ c₁ + M) ε² √ε L`
when `η ≤ c₁ ε L`, `ε ≤ 1`, `L ≥ 1`. -/
theorem p11_slow_f2_numeric {eps s K0 K1 c1 eta M L X F : ℝ} (heps : 0 < eps)
    (hs0 : 0 ≤ s) (hes : eps ≤ s) (hL : 1 ≤ L) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hM : 0 ≤ M)
    (hη : eta ≤ c1 * eps * L) (hX : X ≤ K0 * eps ^ 2 + K1 * (eta * s))
    (hF : F ≤ M * eps ^ 3) :
    eps * X + F ≤ (K0 + K1 * c1 + M) * eps ^ 2 * s * L := by
  have hpos : 0 ≤ eps ^ 2 * s := by positivity
  have e1 : eps * (K0 * eps ^ 2) ≤ K0 * (eps ^ 2 * s) * L := by
    have : eps * eps ^ 2 ≤ eps ^ 2 * s := by nlinarith [sq_nonneg eps]
    calc eps * (K0 * eps ^ 2) = K0 * (eps * eps ^ 2) := by ring
      _ ≤ K0 * (eps ^ 2 * s) := by gcongr
      _ ≤ K0 * (eps ^ 2 * s) * L := le_mul_of_one_le_right (by positivity) hL
  have e2 : eps * (K1 * (eta * s)) ≤ K1 * c1 * (eps ^ 2 * s) * L := by
    calc eps * (K1 * (eta * s)) ≤ eps * (K1 * (c1 * eps * L * s)) := by gcongr
      _ = _ := by ring
  have e3 : F ≤ M * (eps ^ 2 * s) * L := by
    have : eps ^ 3 ≤ eps ^ 2 * s := by
      calc eps ^ 3 = eps ^ 2 * eps := by ring
        _ ≤ _ := by gcongr
    calc F ≤ M * eps ^ 3 := hF
      _ ≤ M * (eps ^ 2 * s) := by gcongr
      _ ≤ M * (eps ^ 2 * s) * L := le_mul_of_one_le_right (by positivity) hL
  have h1 : eps * X ≤ eps * (K0 * eps ^ 2 + K1 * (eta * s)) := by gcongr
  calc eps * X + F ≤ eps * (K0 * eps ^ 2 + K1 * (eta * s)) + F := by gcongr
    _ = eps * (K0 * eps ^ 2) + eps * (K1 * (eta * s)) + F := by ring
    _ ≤ K0 * (eps ^ 2 * s) * L + K1 * c1 * (eps ^ 2 * s) * L + M * (eps ^ 2 * s) * L := by
        gcongr
    _ = _ := by ring

/-- `sup |f₂| ≤ c ε^{5/2} (log 1/ε)^{2τ+1}` on the strip of width `σ/6` over the box
(graph step `as-osc`, oscillation estimate and `|f₁| ≤ (ε M_F)³`). -/
theorem p11_slow_f2_sup (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {c1 : ℝ}
    (hrate : p11eta1 C eps ≤ c1 * eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) :
    ∀ z ∈ KAM.complexStrip (n + n) (C.sigma / 6) ×ˢ p11SlowBox C eps,
      ‖p11SlowF2 C Fast eps (p11SlowZ AR AB) z‖ ≤
        p11SlowC0 C c1 * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hf1, -⟩ := id hF
  obtain ⟨-, -, hARb, -, hAe⟩ := hP
  have hs0 := p11s1_pos hC heps hεM
  rintro z ⟨hz1, hI⟩
  obtain ⟨hJ4, hρ, hre⟩ := p11SlowBox_mem heps hs0 hI
  have hJ2 : ‖p11SlowJ z.2 - KAM.realInclusion n C.J0‖ < p11s1 C eps / 2 := by linarith
  have hJm : p11SlowJ z.2 ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) :=
    mem_ball_iff_norm.2 hJ2
  obtain ⟨hP4, -, hU⟩ := p11_polarC_mem hC heps hsm hz1 hJ2 hρ
  have hosc := p11_slow_osc_pointwise hC Fast hF heps hεM hsm hARb
    (fun z hz hre => (hAe z hz hre).2) hJm hρ hre hP4
  have hf1b := hf1 _ hU
  have hform : p11SlowF2 C Fast eps (p11SlowZ AR AB) z =
      eps * (p11R4 C (p11SlowJ z.2, p11PolPt z) + p11Gbar C Fast (p11SlowJ z.2, p11PolPt z) -
        (AR (p11SlowJ z.2, p11SlowR z.2) + AB (p11SlowJ z.2, p11SlowR z.2))) +
        Fast.f1 (p11PolarC z) := by
    unfold p11SlowF2 p11SlowZ
    rw [p11_slow_G_polar C Fast z]
    ring
  have hε1 : eps ≤ Real.exp (-1) := le_trans (by nlinarith) hεM
  have hε1' : eps ≤ 1 := hε1.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hL : 1 ≤ Real.log (1 / eps) := log_inv_ge_one heps hε1
  have hLa : 1 ≤ Real.log (1 / eps) ^ (2 * C.tau + 1) :=
    Real.one_le_rpow hL (by linarith)
  have he2 : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have he1 : eps ≤ Real.sqrt eps := by
    nlinarith [Real.sqrt_nonneg eps, Real.sqrt_le_one.2 hε1']
  have h52 : eps ^ (5 / 2 : ℝ) = eps ^ 2 * Real.sqrt eps := by
    rw [show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num, Real.rpow_add heps, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
  have hM0 : 0 < C.MF := by linarith
  rw [hform]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg heps.le]
  have hnum := p11_slow_f2_numeric (X := ‖p11R4 C (p11SlowJ z.2, p11PolPt z) +
      p11Gbar C Fast (p11SlowJ z.2, p11PolPt z) -
      (AR (p11SlowJ z.2, p11SlowR z.2) + AB (p11SlowJ z.2, p11SlowR z.2))‖)
    (F := ‖Fast.f1 (p11PolarC z)‖) (M := C.MF ^ 3) (K0 := 256 * C.MF / C.rz ^ 4 +
      2 ^ (2 * n) * 9 * C.MF / (C.rz / 2) ^ 4) (K1 := 12 / (C.rz / 2)) (c1 := c1)
    (eta := p11eta1 C eps) (L := Real.log (1 / eps) ^ (2 * C.tau + 1)) heps
    (Real.sqrt_nonneg _) he1 hLa (by positivity) (by positivity) (by positivity) hrate hosc
    (by rw [← mul_pow, mul_comm]; exact hf1b)
  refine hnum.trans (le_of_eq ?_)
  rw [p11SlowC0, h52]
  ring

end F2

end KAM.Planetary

end
