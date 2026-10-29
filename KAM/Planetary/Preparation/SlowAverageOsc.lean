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

/-- Schwarz bound for `ḡ(J, w) - ḡ(J, 0)` (order-one vanishing at `w = 0`). -/
theorem p11_gbar_osc (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    {J : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2))
    {w : P11Phase n} (hw : ‖w‖ < C.rz / 2) :
    ‖p11Gbar C Fast (J, w) - p11Gbar C Fast (J, 0)‖ ≤
      2 * p11eta1 C eps * (‖w‖ / (C.rz / 2)) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  obtain ⟨hd, hb⟩ := p11_gbar_data hC Fast hF heps hεM
  have hr : 0 < C.rz / 2 := by positivity
  have hm : ∀ z ∈ ball (0 : P11Phase n) (C.rz / 2), (J, z) ∈
      ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ ball (0 : P11Phase n) (C.rz / 2) :=
    fun z hz => ⟨hJ, hz⟩
  have hdz : DifferentiableOn ℂ (fun z : P11Phase n => p11Gbar C Fast (J, z) -
      p11Gbar C Fast (J, 0)) (ball 0 (C.rz / 2)) :=
    ((hd.comp (by fun_prop : DifferentiableOn ℂ (fun z : P11Phase n => (J, z)) _) hm).sub
      (differentiableOn_const _))
  have hbz : ∀ z ∈ ball (0 : P11Phase n) (C.rz / 2),
      ‖p11Gbar C Fast (J, z) - p11Gbar C Fast (J, 0)‖ ≤ 2 * p11eta1 C eps := by
    intro z hz
    have h1 := hb _ (hm z hz)
    have h2 := hb _ (hm 0 (mem_ball_self hr))
    calc _ ≤ ‖p11Gbar C Fast (J, z)‖ + ‖p11Gbar C Fast (J, 0)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hj : ∀ j < 1, iteratedFDeriv ℂ j (fun z : P11Phase n => p11Gbar C Fast (J, z) -
      p11Gbar C Fast (J, 0)) 0 = 0 := by
    intro j hj
    obtain rfl : j = 0 := by omega
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  have := p11_radial_schwarz_gen (k := 1) hr hdz hbz hj w (mem_ball_zero_iff.2 hw)
  simpa using this

/-- The polar average of `ḡ` differs from `ḡ(J, 0)` by `≲ η₁ √(‖ρ̃‖/π)` (order-one Schwarz bound
through `p11PolarAverage_norm_le_pow`, linearity and the normalization of the polar average). -/
theorem p11_gbar_avg_osc (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    {J ρ : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2))
    (hρ : ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2 / 4) (hre : ∀ i, 0 < (ρ i).re) :
    ‖p11PolarAverage (p11Gbar C Fast) (J, ρ) - p11Gbar C Fast (J, 0)‖ ≤
      2 * p11eta1 C eps * (Real.sqrt (‖ρ‖ / Real.pi) / (C.rz / 2)) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  obtain ⟨hd, hb⟩ := p11_gbar_data hC Fast hF heps hεM
  have hη0 := p11eta1_pos hC heps hεM
  have hr : 0 < C.rz / 2 := by positivity
  set Dm : Set (P11CVec n) := ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) with hDm
  set Gb0 : P11CVec n × P11Phase n → ℂ := fun p => p11Gbar C Fast p - p11Gbar C Fast (p.1, 0)
    with hGb0
  set H : P11CVec n × P11Phase n → ℂ := fun p => p11Gbar C Fast (p.1, 0) with hH
  have hDz : ∀ p ∈ Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2), (p.1, (0 : P11Phase n)) ∈
      Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2) := fun p hp => ⟨hp.1, mem_ball_self hr⟩
  have hHd : DifferentiableOn ℂ H (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) :=
    hd.comp (by fun_prop : DifferentiableOn ℂ
      (fun p : P11CVec n × P11Phase n => (p.1, (0 : P11Phase n))) _) hDz
  have hGb0d : DifferentiableOn ℂ Gb0 (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) := hd.sub hHd
  have hGb0b : p11Bound (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) Gb0 (2 * p11eta1 C eps) := by
    intro p hp
    have h1 := hb p hp
    have h2 := hb _ (hDz p hp)
    calc _ ≤ ‖p11Gbar C Fast p‖ + ‖p11Gbar C Fast (p.1, 0)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hj : ∀ J ∈ Dm, ∀ j < 1, iteratedFDeriv ℂ j (fun z : P11Phase n => Gb0 (J, z)) 0 = 0 := by
    intro J _ j hj
    obtain rfl : j = 0 := by omega
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp [hGb0]
  have hρ1 : ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2 := by
    have : 0 < Real.pi * (C.rz / 2) ^ 2 := by positivity
    linarith
  have hnorm := p11PolarAverage_norm_le_pow hr (by positivity) hGb0d hGb0b hj hJ hρ1
  have hz : (J, ρ) ∈ Dm ×ˢ ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4) :=
    ⟨hJ, mem_ball_zero_iff.2 hρ⟩
  have hlin := polar_average_linear (D := Dm) isOpen_ball hr hGb0d hHd 1 1 (J, ρ) hz hre
  have hfun : (1 : ℂ) • Gb0 + (1 : ℂ) • H = p11Gbar C Fast := by
    funext p
    simp [hGb0, hH]
  rw [hfun] at hlin
  have hnorm' := (polar_average_normalization (fun J : P11CVec n => p11Gbar C Fast (J, 0))
    (J, ρ)).1
  have heq : p11PolarAverage (p11Gbar C Fast) (J, ρ) - p11Gbar C Fast (J, 0) =
      p11PolarAverage Gb0 (J, ρ) := by
    rw [hlin, one_mul, one_mul]
    have : p11PolarAverage H (J, ρ) = p11Gbar C Fast (J, 0) := hnorm'
    rw [this]; ring
  rw [heq]
  simpa using hnorm


/-- Pointwise oscillation estimate (graph step `as-osc`): on the polar region,
`‖(R₄ + ḡ)(J, Π) - (AR + AB)(J, ρ̃)‖ ≤ c₀ ε² + c₁ η₁ √ε` with `‖Π‖ ≤ 4 √ε`, `‖ρ̃‖ < 3πε`. -/
theorem p11_slow_osc_pointwise (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsm : 64 * eps < C.rz ^ 2) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hARb : ∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4),
      ‖AR z‖ ≤ 2 ^ (2 * n) * (C.MF / 16) * (4 * ‖z.2‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2)
    (hABe : ∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4), (∀ i, 0 < (z.2 i).re) →
      AB z = p11PolarAverage (p11Gbar C Fast) z)
    {J ρ : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2))
    (hρ : ‖ρ‖ < 3 * Real.pi * eps) (hre : ∀ i, 0 < (ρ i).re)
    {Pt : P11Phase n} (hPt : ‖Pt‖ ≤ 4 * Real.sqrt eps) :
    ‖p11R4 C (J, Pt) + p11Gbar C Fast (J, Pt) - (AR (J, ρ) + AB (J, ρ))‖ ≤
      (256 * C.MF / C.rz ^ 4 + 2 ^ (2 * n) * 9 * C.MF / (C.rz / 2) ^ 4) * eps ^ 2 +
        12 / (C.rz / 2) * (p11eta1 C eps * Real.sqrt eps) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hη0 := p11eta1_pos hC heps hεM
  have hr : 0 < C.rz / 2 := by positivity
  have he0 : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have he2 : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have hpi := Real.pi_pos
  have hPtr : ‖Pt‖ < C.rz / 2 := by
    refine lt_of_le_of_lt hPt ?_
    have : (4 * Real.sqrt eps) ^ 2 < (C.rz / 2) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hr.le this
  have hρD : ‖ρ‖ < Real.pi * (C.rz / 2) ^ 2 / 4 := by nlinarith
  have hz : (J, ρ) ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
      ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4) := ⟨hJ, mem_ball_zero_iff.2 hρD⟩
  have hJ2 : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    ball_subset_ball (by linarith [p11s1_le C eps, p11s1_pos hC heps hεM]) hJ
  -- the four pieces
  have T1 : ‖p11R4 C (J, Pt)‖ ≤ 256 * C.MF / C.rz ^ 4 * eps ^ 2 := by
    refine (p11R4_bound hC hJ2 (hPtr.trans (by linarith))).trans ?_
    have h4 : ‖Pt‖ ^ 4 ≤ (4 * Real.sqrt eps) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hPt 4
    have : (4 * Real.sqrt eps) ^ 4 = 256 * eps ^ 2 := by
      rw [mul_pow, show (4 : ℝ) ^ 4 = 256 by norm_num,
        show Real.sqrt eps ^ 4 = (Real.sqrt eps ^ 2) ^ 2 by ring, he2]
    calc C.MF / C.rz ^ 4 * ‖Pt‖ ^ 4 ≤ C.MF / C.rz ^ 4 * (256 * eps ^ 2) := by
          rw [← this]; gcongr
      _ = _ := by ring
  have T2 : ‖AR (J, ρ)‖ ≤ 2 ^ (2 * n) * 9 * C.MF / (C.rz / 2) ^ 4 * eps ^ 2 := by
    refine (hARb _ hz).trans ?_
    simp only
    have hr2 : 0 < Real.pi * (C.rz / 2) ^ 2 := by positivity
    have h1 : 4 * ‖ρ‖ / (Real.pi * (C.rz / 2) ^ 2) ≤ 12 * eps / (C.rz / 2) ^ 2 := by
      rw [div_le_div_iff₀ hr2 (by positivity)]
      nlinarith [pow_pos hr 2]
    have h2 : (4 * ‖ρ‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2 ≤ (12 * eps / (C.rz / 2) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc 2 ^ (2 * n) * (C.MF / 16) * (4 * ‖ρ‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2
        ≤ 2 ^ (2 * n) * (C.MF / 16) * (12 * eps / (C.rz / 2) ^ 2) ^ 2 := by gcongr
      _ = _ := by field_simp; ring
  have T3 := p11_gbar_osc hC Fast hF heps hεM hJ hPtr
  have T4 := p11_gbar_avg_osc hC Fast hF heps hεM hJ hρD hre
  have hAB : AB (J, ρ) = p11PolarAverage (p11Gbar C Fast) (J, ρ) := hABe _ hz hre
  rw [hAB]
  have hs3 : Real.sqrt (‖ρ‖ / Real.pi) ≤ 2 * Real.sqrt eps := by
    have : ‖ρ‖ / Real.pi ≤ (2 * Real.sqrt eps) ^ 2 := by
      rw [div_le_iff₀ hpi]; nlinarith
    exact (Real.sqrt_le_left (by positivity)).2 this
  have T3' : ‖p11Gbar C Fast (J, Pt) - p11Gbar C Fast (J, 0)‖ ≤
      8 / (C.rz / 2) * (p11eta1 C eps * Real.sqrt eps) := by
    refine T3.trans ?_
    have : ‖Pt‖ / (C.rz / 2) ≤ 4 * Real.sqrt eps / (C.rz / 2) :=
      div_le_div_of_nonneg_right hPt hr.le
    calc 2 * p11eta1 C eps * (‖Pt‖ / (C.rz / 2))
        ≤ 2 * p11eta1 C eps * (4 * Real.sqrt eps / (C.rz / 2)) := by gcongr
      _ = _ := by field_simp; ring
  have T4' : ‖p11PolarAverage (p11Gbar C Fast) (J, ρ) - p11Gbar C Fast (J, 0)‖ ≤
      4 / (C.rz / 2) * (p11eta1 C eps * Real.sqrt eps) := by
    refine T4.trans ?_
    have : Real.sqrt (‖ρ‖ / Real.pi) / (C.rz / 2) ≤ 2 * Real.sqrt eps / (C.rz / 2) :=
      div_le_div_of_nonneg_right hs3 hr.le
    calc 2 * p11eta1 C eps * (Real.sqrt (‖ρ‖ / Real.pi) / (C.rz / 2))
        ≤ 2 * p11eta1 C eps * (2 * Real.sqrt eps / (C.rz / 2)) := by gcongr
      _ = _ := by field_simp; ring
  have hsplit : p11R4 C (J, Pt) + p11Gbar C Fast (J, Pt) -
      (AR (J, ρ) + p11PolarAverage (p11Gbar C Fast) (J, ρ)) =
      p11R4 C (J, Pt) - AR (J, ρ) +
        ((p11Gbar C Fast (J, Pt) - p11Gbar C Fast (J, 0)) -
          (p11PolarAverage (p11Gbar C Fast) (J, ρ) - p11Gbar C Fast (J, 0))) := by ring
  rw [hsplit]
  calc _ ≤ ‖p11R4 C (J, Pt) - AR (J, ρ)‖ + ‖(p11Gbar C Fast (J, Pt) - p11Gbar C Fast (J, 0)) -
          (p11PolarAverage (p11Gbar C Fast) (J, ρ) - p11Gbar C Fast (J, 0))‖ := norm_add_le _ _
    _ ≤ (‖p11R4 C (J, Pt)‖ + ‖AR (J, ρ)‖) + (‖p11Gbar C Fast (J, Pt) - p11Gbar C Fast (J, 0)‖ +
          ‖p11PolarAverage (p11Gbar C Fast) (J, ρ) - p11Gbar C Fast (J, 0)‖) :=
        add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ _ := by
      have : 12 / (C.rz / 2) * (p11eta1 C eps * Real.sqrt eps) =
          8 / (C.rz / 2) * (p11eta1 C eps * Real.sqrt eps) +
            4 / (C.rz / 2) * (p11eta1 C eps * Real.sqrt eps) := by ring
      nlinarith [T1, T2, T3', T4']

end Osc

end KAM.Planetary

end
