/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.EquationComplex
public import KAM.Planetary.Preparation.SlowSigned
public import KAM.Planetary.Preparation.SlowAverageReal

/-!
# Source objects of Step D (`bpP:p11:sec-D#data`, package P-SEC)

The literal objects of display `(par2)` of blueprint-P Part 11, with their identifications:

* `p11PolarShell` is `𝒫_ε = {|Im ζ|_∞ < σ_F/6, |ρ̃_j - 2πε| < πε}`, with its characterizations;
* `p11Pi` is `Π(ζ, ρ̃) = Θ^{(1)}(ζ, ρ̃) = (√(ρ̃/π) sin 2πζ, √(ρ̃/π) cos 2πζ)`, identified with the
  fast block of `p11PolarC` and with `p11PolPt`, bounded by `√(3ε) e^{πσ_F/3}` on `𝒫_ε`;
* `p11GHat`, `p11GHat0` are `Ĝ = G(J, Π)` and the raw `ζ`-average `Ĝ₀ = ∫ Ĝ dζ`
  (`= p11PolarAverage G` by `rfl`);
* `p11SourceH0 = h̃ + ε Ĝ₀`, `p11SourceF2 = ε (Ĝ - Ĝ₀) + f₁ ∘ (id, Π)`;
* the helpers `p11SlowH0`, `p11SlowF2` equal the source objects exactly when the correction is
  `Ẑ = Ĝ₀ - C - Σ Ω̃ ρ̃`, which holds for `Ẑ = p11SlowZ AR AB = 𝒜R₄ + 𝒜ḡ` on the box;
* the chosen datum (`P11SlowSpecOf`, and `p11SlowData` under its guard) has `h₀`, `f₂` equal to
  the source objects on the whole of `T_{σ₃} × V₂`;
* `σ₃ = σ_F/12`, `α_(1)`, `α_(2)`, and `e^{-2π K₂ σ₃/6} = ε^{ν₂}`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section SecD

variable {n : ℕ}

/-- `σ₃ = σ_F/12`. -/
def p11Sigma3 (C : P11SecularData n) : ℝ := C.sigma / 12

/-- The polar shell `𝒫_ε = {(ζ, ρ̃) : |Im ζ|_∞ < σ_F/6, ∀ j, |ρ̃_j - 2πε| < πε}`. -/
def p11PolarShell (C : P11SecularData n) (eps : ℝ) : Set (P11CVec n × P11CVec n) :=
  {p | (∀ i, |(p.1 i).im| < C.sigma / 6) ∧
    ∀ j, ‖p.2 j - (2 * Real.pi * eps : ℂ)‖ < Real.pi * eps}

theorem mem_p11PolarShell {C : P11SecularData n} {eps : ℝ} {p : P11CVec n × P11CVec n} :
    p ∈ p11PolarShell C eps ↔ (∀ i, |(p.1 i).im| < C.sigma / 6) ∧
      ∀ j, ‖p.2 j - (2 * Real.pi * eps : ℂ)‖ < Real.pi * eps := Iff.rfl

theorem p11PolarShell_eq_prod (C : P11SecularData n) (eps : ℝ) :
    p11PolarShell C eps = KAM.complexStrip n (C.sigma / 6) ×ˢ
      {ρ : P11CVec n | ∀ j, ‖ρ j - (2 * Real.pi * eps : ℂ)‖ < Real.pi * eps} := rfl

theorem p11PolarShell_isOpen (C : P11SecularData n) (eps : ℝ) :
    IsOpen (p11PolarShell C eps) := by
  have h1 : ∀ i, IsOpen {p : P11CVec n × P11CVec n | |(p.1 i).im| < C.sigma / 6} := fun i =>
    isOpen_lt (by fun_prop) continuous_const
  have h2 : ∀ j, IsOpen {p : P11CVec n × P11CVec n |
      ‖p.2 j - (2 * Real.pi * eps : ℂ)‖ < Real.pi * eps} := fun j =>
    isOpen_lt (by fun_prop) continuous_const
  have : p11PolarShell C eps = (⋂ i, {p : P11CVec n × P11CVec n | |(p.1 i).im| < C.sigma / 6}) ∩
      ⋂ j, {p : P11CVec n × P11CVec n | ‖p.2 j - (2 * Real.pi * eps : ℂ)‖ < Real.pi * eps} := by
    ext p; simp [p11PolarShell]
  rw [this]
  exact (isOpen_iInter_of_finite h1).inter (isOpen_iInter_of_finite h2)

/-- On `𝒫_ε`: `Re ρ̃_j > πε` (so the principal square root is holomorphic there). -/
theorem p11PolarShell_re_gt {C : P11SecularData n} {eps : ℝ} {p : P11CVec n × P11CVec n}
    (hp : p ∈ p11PolarShell C eps) (j : Fin n) : Real.pi * eps < (p.2 j).re := by
  have h1 := Complex.abs_re_le_norm (p.2 j - (2 * Real.pi * eps : ℂ))
  have h3 : (p.2 j - (2 * Real.pi * eps : ℂ)).re = (p.2 j).re - 2 * Real.pi * eps := by simp
  rw [h3] at h1
  linarith [(abs_lt.1 (h1.trans_lt (hp.2 j))).1]

/-- On `𝒫_ε`: `|ρ̃_j| < 3πε`. -/
theorem p11PolarShell_norm_lt {C : P11SecularData n} {eps : ℝ} {p : P11CVec n × P11CVec n}
    (hp : p ∈ p11PolarShell C eps) (j : Fin n) : ‖p.2 j‖ < 3 * Real.pi * eps := by
  have hle : ‖p.2 j‖ ≤ ‖p.2 j - (2 * Real.pi * eps : ℂ)‖ + ‖(2 * Real.pi * eps : ℂ)‖ :=
    norm_le_norm_sub_add _ _
  have hpe : 0 ≤ Real.pi * eps := (norm_nonneg _).trans (hp.2 j).le
  have h2 : ‖(2 * Real.pi * eps : ℂ)‖ = 2 * Real.pi * eps := by
    rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  linarith [hp.2 j]

/-- `Π(ζ, ρ̃) = (√(ρ̃/π) sin 2πζ, √(ρ̃/π) cos 2πζ)` (`Θ^{(1)}`, principal square roots). -/
def p11Pi (zeta rho : P11CVec n) : P11Phase n :=
  ((fun i => Complex.sqrt (rho i / Real.pi) * Complex.sin (2 * Real.pi * zeta i)),
    fun i => Complex.sqrt (rho i / Real.pi) * Complex.cos (2 * Real.pi * zeta i))

/-- The oscillator angles `ζ` of a full phase point. -/
def p11SlowZeta (z : P11CVec (n + n)) : P11CVec n := fun i => z (Fin.natAdd n i)

/-- `p11PolPt` is `Π(ζ, ρ̃)`. -/
theorem p11PolPt_eq_pi (z : P11Phase (n + n)) :
    p11PolPt z = p11Pi (p11SlowZeta z.1) (p11SlowR z.2) := by
  ext i <;> simp [p11PolPt, p11PolarC, p11Pi, p11SlowZeta, p11SlowR]

/-- `p11PolarC = (id_{θ,J}, Π)`: the slow block is unchanged, the fast block is `Π`. -/
theorem p11PolarC_eq_pi (z : P11Phase (n + n)) :
    p11PolarC z = (Fin.append (fun i : Fin n => z.1 (Fin.castAdd n i))
        (p11Pi (p11SlowZeta z.1) (p11SlowR z.2)).1,
      Fin.append (p11SlowJ z.2) (p11Pi (p11SlowZeta z.1) (p11SlowR z.2)).2) := rfl

/-- `|Π|_∞ ≤ √(3ε) e^{πσ_F/3}` on `𝒫_ε`. -/
theorem p11Pi_norm_le {C : P11SecularData n} {eps : ℝ} {p : P11CVec n × P11CVec n}
    (hp : p ∈ p11PolarShell C eps) (hσ : 0 ≤ C.sigma) :
    ‖p11Pi p.1 p.2‖ ≤ Real.sqrt (3 * eps) * Real.exp (Real.pi * C.sigma / 3) := by
  have hy : ∀ i, |(2 * Real.pi * p.1 i).im| ≤ Real.pi * C.sigma / 3 := fun i => by
    have h := (hp.1 i).le
    have : (2 * Real.pi * p.1 i).im = 2 * Real.pi * (p.1 i).im := by simp
    rw [this, abs_mul, abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_pos]
  have hch : Real.cosh (Real.pi * C.sigma / 3) ≤ Real.exp (Real.pi * C.sigma / 3) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(Real.pi * C.sigma / 3)) ≤ Real.exp (Real.pi * C.sigma / 3) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    linarith
  have hs : ∀ i, ‖Complex.sqrt (p.2 i / Real.pi)‖ ≤ Real.sqrt (3 * eps) := fun i => by
    rw [p11_norm_sqrt_eq]
    refine Real.sqrt_le_sqrt ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      div_le_iff₀ Real.pi_pos]
    linarith [p11PolarShell_norm_lt hp i]
  have h0 : 0 ≤ Real.sqrt (3 * eps) * Real.exp (Real.pi * C.sigma / 3) := by positivity
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg h0).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg h0).2 fun i => ?_)
  · simp only [p11Pi, norm_mul]
    exact mul_le_mul (hs i) ((KAM.Kepler.EqC.norm_sin_le (hy i)).trans hch) (norm_nonneg _)
      (Real.sqrt_nonneg _)
  · simp only [p11Pi, norm_mul]
    exact mul_le_mul (hs i) ((KAM.Kepler.EqC.norm_cos_le (hy i)).trans hch) (norm_nonneg _)
      (Real.sqrt_nonneg _)

/-- `Ĝ(J, ζ, ρ̃) = G(J, Π(ζ, ρ̃))`. -/
def p11GHat (Fast : P11FastData n) (J zeta rho : P11CVec n) : ℂ := Fast.G (J, p11Pi zeta rho)

/-- `Ĝ₀(J, ρ̃) = ∫_{𝕋ⁿ} Ĝ(J, ζ, ρ̃) dζ` (raw `ζ`-average over real `ζ`). -/
def p11GHat0 (Fast : P11FastData n) (J rho : P11CVec n) : ℂ :=
  KAM.torusAverage (fun zeta : P11Vec n => p11GHat Fast J (fun i => (zeta i : ℂ)) rho)

/-- The raw `ζ`-average is the polar average of `G`. -/
theorem p11GHat0_eq_polarAverage (Fast : P11FastData n) (J rho : P11CVec n) :
    p11GHat0 Fast J rho = p11PolarAverage Fast.G (J, rho) := rfl

/-- Source `h₀(J, ρ̃) = h̃(J) + ε Ĝ₀(J, ρ̃)`. -/
def p11SourceH0 (C : P11SecularData n) (Fast : P11FastData n) (eps : ℝ)
    (I : P11CVec (n + n)) : ℂ :=
  C.h (p11SlowJ I) + eps * p11GHat0 Fast (p11SlowJ I) (p11SlowR I)

/-- Source `f₂ = ε (Ĝ - Ĝ₀) + f₁ ∘ (id, Π)`. -/
def p11SourceF2 (Fast : P11FastData n) (eps : ℝ)
    (z : P11Phase (n + n)) : ℂ :=
  eps * (p11GHat Fast (p11SlowJ z.2) (p11SlowZeta z.1) (p11SlowR z.2) -
      p11GHat0 Fast (p11SlowJ z.2) (p11SlowR z.2)) + Fast.f1 (p11PolarC z)

/-- The helper `h₀` with correction `Z` is the source `h₀` iff `C + Σ Ω ρ̃/2π + Z = Ĝ₀`. -/
theorem p11SlowH0_eq_source_iff (C : P11SecularData n) (Fast : P11FastData n) {eps : ℝ}
    (heps : eps ≠ 0) (Z : P11CVec (n + n) → ℂ) (I : P11CVec (n + n)) :
    p11SlowH0 C eps Z I = p11SourceH0 C Fast eps I ↔
      p11SlowSec C I + Z I = p11GHat0 Fast (p11SlowJ I) (p11SlowR I) := by
  have he : (eps : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 heps
  simp only [p11SlowH0, p11SourceH0]
  constructor
  · intro h; exact mul_left_cancel₀ he (add_left_cancel h)
  · intro h; rw [h]; rfl

/-- The helper `f₂` with correction `Z` is the source `f₂` iff `C + Σ Ω ρ̃/2π + Z = Ĝ₀`. -/
theorem p11SlowF2_eq_source_iff (C : P11SecularData n) (Fast : P11FastData n) {eps : ℝ}
    (heps : eps ≠ 0) (Z : P11CVec (n + n) → ℂ) (z : P11Phase (n + n)) :
    p11SlowF2 C Fast eps Z z = p11SourceF2 Fast eps z ↔
      p11SlowSec C z.2 + Z z.2 = p11GHat0 Fast (p11SlowJ z.2) (p11SlowR z.2) := by
  have he : (eps : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 heps
  simp only [p11SlowF2, p11SourceF2, p11GHat, ← p11PolPt_eq_pi]
  constructor
  · intro h
    have h' := sub_right_injective (mul_left_cancel₀ he (add_right_cancel h))
    exact h'
  · intro h; rw [h]

variable {D : P11Physical n} {C : P11SecularData n}

/-- The implementation correction `Ẑ = 𝒜R₄ + 𝒜ḡ` is the source one on the box
`D(J₀, s₁/4) × D(2πε, πε)`: `Ĝ₀ = C + Σ Ω̃ ρ̃ + Ẑ`. -/
theorem p11GHat0_eq_sec_add_Z (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {I : P11CVec (n + n)}
    (hI : I ∈ p11SlowAvgBox C eps) :
    p11GHat0 Fast (p11SlowJ I) (p11SlowR I) = p11SlowSec C I + p11SlowZ AR AB I :=
  (p11_slow_secZ_eq hC Fast hF hP heps hεM hsm hI).symm

/-- With `Ẑ = p11SlowZ AR AB`, the helper `h₀` is the source `h₀ = h̃ + ε Ĝ₀` on the box. -/
theorem p11SlowH0_eq_source (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {I : P11CVec (n + n)}
    (hI : I ∈ p11SlowAvgBox C eps) :
    p11SlowH0 C eps (p11SlowZ AR AB) I = p11SourceH0 C Fast eps I :=
  (p11SlowH0_eq_source_iff C Fast heps.ne' _ I).2 (p11_slow_secZ_eq hC Fast hF hP heps hεM hsm hI)

/-- With `Ẑ = p11SlowZ AR AB`, the helper `f₂` is the source `f₂ = ε(Ĝ - Ĝ₀) + f₁ ∘ (id, Π)`
at every point whose action lies in the box. -/
theorem p11SlowF2_eq_source (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) {AR AB : P11CVec n × P11CVec n → ℂ}
    (hP : P11SlowPolarOut C Fast eps AR AB) (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 64 * eps < C.rz ^ 2) {z : P11Phase (n + n)}
    (hz : z.2 ∈ p11SlowAvgBox C eps) :
    p11SlowF2 C Fast eps (p11SlowZ AR AB) z = p11SourceF2 Fast eps z :=
  (p11SlowF2_eq_source_iff C Fast heps.ne' _ z).2 (p11_slow_secZ_eq hC Fast hF hP heps hεM hsm hz)

/-- The chosen datum's `h₀` is the source `h₀ = h̃ + ε Ĝ₀` on all of `V₂`. -/
theorem P11SlowSpecOf.h0_eq_source {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hA : P11SlowSpecOf C Fast nu eps c A) {I : P11CVec (n + n)}
    (hI : I ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) :
    A.h0 I = p11SourceH0 C Fast eps I :=
  hA.2.1 I hI

/-- The chosen datum's `f₂` is the source `f₂ = ε(Ĝ - Ĝ₀) + f₁ ∘ (id, Π)` on all of
`T_{σ₃} × V₂`. -/
theorem P11SlowSpecOf.f2_eq_source (hC : P11SecularSpec D C) {Fast : P11FastData n}
    {nu eps c : ℝ} (hF : P11FastSpec C eps Fast) {A : P11SlowData n}
    (hA : P11SlowSpecOf C Fast nu eps c A) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hsm : 64 * eps < C.rz ^ 2) {z : P11Phase (n + n)}
    (hz : z ∈ KAM.complexStrip (n + n) (p11Sigma3 C) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi * eps)) :
    A.f2 z = p11SourceF2 Fast eps z := by
  obtain ⟨-, -, -, -, -, hσ0, -⟩ := fast_consts hC
  have hs1 := p11s1_pos hC heps hεM
  have hbox : z.2 ∈ p11SlowAvgBox C eps :=
    ⟨fun i => (hz.2.1 i).trans_le (min_le_left _ _), hz.2.2⟩
  obtain ⟨hJ, hρ, -⟩ := p11SlowAvgBox_mem heps hs1 hbox
  have hstrip : z.1 ∈ KAM.complexStrip (n + n) (C.sigma / 6) := fun i =>
    (hz.1 i).trans_le (by unfold p11Sigma3; linarith)
  obtain ⟨-, -, hU⟩ := p11_polarC_mem hC heps hsm hstrip (by linarith) hρ
  have h1 := hA.1 z hz
  have h2 := hA.2.1 z.2 hz.2
  have h3 := hF.2.2.2.2.2.2.2.2.2.2.1 _ hU
  have hpc : (fun i : Fin n => (p11PolarC z).2 (Fin.castAdd n i)) = p11SlowJ z.2 := by
    funext i; simp [p11PolarC, p11SlowJ, Fin.append_left]
  have hpp : ((fun i : Fin n => (p11PolarC z).1 (Fin.natAdd n i)),
      fun i : Fin n => (p11PolarC z).2 (Fin.natAdd n i)) = p11PolPt z := rfl
  rw [hpc, hpp, p11PolPt_eq_pi] at h3
  have key : A.f2 z = p11WorkingH C eps (Fast.map (p11PolarC z)) - A.h0 z.2 := by
    rw [← h1]; ring
  rw [key, h3, h2]
  simp only [p11SourceF2, p11GHat, p11GHat0_eq_polarAverage]
  rw [show (fun i : Fin n => z.2 (Fin.castAdd n i)) = p11SlowJ z.2 from rfl,
    show (fun i : Fin n => z.2 (Fin.natAdd n i)) = p11SlowR z.2 from rfl]
  ring

/-- The signed `p11SlowData` (under its choice guard and the fast guard) has `h₀`, `f₂` equal to
the source objects on `T_{σ₃} × V₂`. -/
theorem p11SlowData_h0_f2_eq_source {D : P11Physical n} {nu eps : ℝ}
    (hS : ∃ A, P11SlowSpec D nu eps (p11SlowConstant D nu) A)
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps)) (heps : 0 < eps)
    (hεM : eps * (p11SecularData D).MF ≤ Real.exp (-1))
    (hsm : 64 * eps < (p11SecularData D).rz ^ 2) :
    (∀ I ∈ p11Box (p11SlowCenter (p11SecularData D) eps) (p11s2 (p11SecularData D) nu eps)
        (Real.pi * eps),
      (p11SlowData D nu eps).h0 I = p11SourceH0 (p11SecularData D) (p11FastData D eps) eps I) ∧
    ∀ z ∈ KAM.complexStrip (n + n) (p11Sigma3 (p11SecularData D)) ×ˢ
        p11Box (p11SlowCenter (p11SecularData D) eps) (p11s2 (p11SecularData D) nu eps)
          (Real.pi * eps),
      (p11SlowData D nu eps).f2 z = p11SourceF2 (p11FastData D eps) eps z := by
  have hA : P11SlowSpecOf (p11SecularData D) (p11FastData D eps) nu eps (p11SlowConstant D nu)
      (p11SlowData D nu eps) := by
    unfold p11SlowData
    split
    · rename_i h; exact h.choose_spec
    · exact absurd hS ‹_›
  exact ⟨fun I hI => hA.h0_eq_source hI, fun z hz =>
    hA.f2_eq_source (holo_chart D).choose_spec.1 hF heps hεM hsm hz⟩

/-- `α_(1) = γ₀ K₂^{-τ₀}/4`. -/
def p11Alpha21 (C : P11SecularData n) (nu eps : ℝ) : ℝ :=
  C.gamma * p11K2 C nu eps ^ (-C.tau) / 4

/-- `α_(2) = ε γ₀ K₂^{-τ₀}/4`. -/
def p11Alpha22 (C : P11SecularData n) (nu eps : ℝ) : ℝ :=
  eps * C.gamma * p11K2 C nu eps ^ (-C.tau) / 4

/-- The divisor lower bound of the slow specification is `α_(2)` on pure slow modes and `α_(1)`
otherwise. -/
theorem p11_slow_divisor_alpha (C : P11SecularData n) (nu eps : ℝ) (P : Prop) [Decidable P] :
    (if P then eps else 1) * C.gamma / 4 * p11K2 C nu eps ^ (-C.tau) =
      if P then p11Alpha22 C nu eps else p11Alpha21 C nu eps := by
  unfold p11Alpha21 p11Alpha22
  split_ifs <;> ring

/-- `K₂ = 3ν₂/(πσ₃) log(1/ε)` and `s₂ = min{s₁/4, γ₀/(8 L K₂^{τ₀+1})}` (definitional). -/
theorem p11K2_s2_eq (C : P11SecularData n) (nu eps : ℝ) :
    p11K2 C nu eps = 3 * nu / (Real.pi * p11Sigma3 C) * Real.log (1 / eps) ∧
      p11s2 C nu eps =
        min (p11s1 C eps / 4) (C.gamma / (8 * C.L * p11K2 C nu eps ^ (C.tau + 1))) :=
  ⟨rfl, rfl⟩

/-- `e^{-2π K₂ σ₃/6} = ε^{ν₂}`. -/
theorem p11_exp_K2 (C : P11SecularData n) (hσ : 0 < C.sigma) (nu : ℝ) {eps : ℝ}
    (heps : 0 < eps) :
    Real.exp (-(2 * Real.pi * p11K2 C nu eps * p11Sigma3 C / 6)) = eps ^ nu := by
  rw [Real.rpow_def_of_pos heps]
  congr 1
  unfold p11K2 p11Sigma3
  rw [one_div, Real.log_inv]
  field_simp
  ring

end SecD

end KAM.Planetary

end
