/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowJets
public import KAM.Planetary.Preparation.Fast
public import KAM.Planetary.Preparation.PolarAverage
public import KAM.Planetary.Preparation.PolarAverage.ParamIntegral

/-!
# Slow averaging: the secular mean and the quartic remainder (P11A-P7, `as-osc` inputs)

For a package `C` with `P11SecularSpec D C`: the constant `C.C` equals the fast mean at the
origin (hence is holomorphic), the fast mean is jointly holomorphic, and
`p11R4 C = FastMean - C - ΣΩ (x²+y²)/2` is holomorphic with vanishing jets of order `< 4`.
`p11Gbar C Fast = G - FastMean` is the fast-averaging remainder (`ε ḡ`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Mean

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

theorem p11WorkingDom_isOpen (J0 : P11Vec n) (s r rz : ℝ) :
    IsOpen (p11WorkingDom n J0 s r rz) := by
  have h1 : IsOpen {z : P11Phase (n+n) | (fun i : Fin n => z.1 (Fin.castAdd n i)) ∈
      KAM.complexStrip n s} :=
    (KAM.isOpen_complexStrip n s).preimage (by fun_prop)
  have h2 : IsOpen {z : P11Phase (n+n) |
      ‖(fun i : Fin n => z.2 (Fin.castAdd n i)) - KAM.realInclusion n J0‖ < r} :=
    isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {z : P11Phase (n+n) | ‖(fun i : Fin n => z.1 (Fin.natAdd n i))‖ < rz} :=
    isOpen_lt (by fun_prop) continuous_const
  have h4 : IsOpen {z : P11Phase (n+n) | ‖(fun i : Fin n => z.2 (Fin.natAdd n i))‖ < rz} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- The components of `P11SecularSpec` used by the slow averaging. -/
theorem secular_extract (hC : P11SecularSpec D C) :
    DifferentiableOn ℂ C.Omega (ball (KAM.realInclusion n C.J0) (2 * C.rC)) ∧
    DifferentiableOn ℂ C.F (p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz) ∧
    p11Bound (p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz) C.F
      (C.MF / KAM.Weighted.coth (Real.pi * C.sigma) ^ n) ∧
    (∀ J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC), ∀ z : P11Phase n, ‖z‖ < C.rz →
      ‖p11FastMean C.F J z - C.C J - ∑ i, C.Omega J i * (z.1 i ^ 2 + z.2 i ^ 2) / 2‖ ≤
        C.MF * (‖z‖ / C.rz) ^ 4) ∧
    (∀ J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC),
      ‖(2 * Real.pi : ℂ)⁻¹ • C.Omega J‖ ≤ C.L) := by
  obtain ⟨-, -, ⟨-, hOm⟩, -, -, -, h7, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFd, hFb, -, -,
    hmean, -⟩ := hC
  refine ⟨hOm, hFd, hFb, hmean, fun J hJ => ?_⟩
  have := h7 J hJ 0 (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero] at this
  refine le_trans ?_ this
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h2 := norm_le_pi_norm (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J))
    (Fin.natAdd n i)
  simpa [Fin.append_right] using h2

/-- The fast mean is holomorphic in `(J, z)` where the working function is. -/
theorem p11FastMean_differentiableOn (hC : P11SecularSpec D C) :
    DifferentiableOn ℂ (fun p : P11CVec n × P11Phase n => p11FastMean C.F p.1 p.2)
      (ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz) := by
  obtain ⟨-, hFd, -⟩ := secular_extract hC
  let Φ : (P11CVec n × P11Phase n) × P11CVec n → P11Phase (n + n) := fun x =>
    (Fin.append x.2 x.1.2.1, Fin.append x.1.1 x.1.2.2)
  have hΦ : Differentiable ℂ Φ := by
    intro x
    refine DifferentiableAt.prodMk ?_ ?_
    · exact differentiableAt_append (by fun_prop) (by fun_prop)
    · exact differentiableAt_append (by fun_prop) (by fun_prop)
  let W := Φ ⁻¹' (p11WorkingDom n C.J0 (2 * C.sigma) (2 * C.rC) C.rz)
  have hWo : IsOpen W := (p11WorkingDom_isOpen _ _ _ _).preimage hΦ.continuous
  have hf : DifferentiableOn ℂ (fun x => C.F (Φ x)) W := hFd.comp hΦ.differentiableOn
    (fun x hx => hx)
  have hmem : ∀ q ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz,
      ∀ θ ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1),
        (q, KAM.realInclusion n θ) ∈ W := by
    rintro q ⟨hq1, hq2⟩ θ -
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff] at hq2
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨-, -, -, -, -, hσ0, -⟩ := fast_consts hC
      have := KAM.ofReal_mem_complexStrip (n := n) (ρ := 2 * C.sigma) (by linarith) θ
      simpa [Φ, Fin.append_left] using this
    · simpa [Φ, Fin.append_left] using mem_ball_iff_norm.1 hq1
    · simpa [Φ, Fin.append_right] using hq2.1
    · simpa [Φ, Fin.append_right] using hq2.2
  haveI : BorelSpace (P11CVec n × P11Phase n) := Prod.borelSpace
  exact p11_differentiableOn_paramIntegral (μ := volume)
    (K := Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) (by
      rw [pi_univ_Icc]; exact isCompact_Icc) (γ := KAM.realInclusion n)
    (KAM.realInclusion n).continuous (isOpen_ball.prod isOpen_ball) hWo hf hmem

/-- At the origin of the fibre the remainder bound pins `C.C` to the fast mean. -/
theorem p11C_eq_fastMean (hC : P11SecularSpec D C) {J : P11CVec n}
    (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) :
    C.C J = p11FastMean C.F J 0 := by
  obtain ⟨-, -, -, hmean, -⟩ := secular_extract hC
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  have h := hmean J hJ 0 (by simpa using hrz0)
  simp at h
  exact (sub_eq_zero.1 h).symm

theorem p11C_differentiableOn (hC : P11SecularSpec D C) :
    DifferentiableOn ℂ C.C (ball (KAM.realInclusion n C.J0) (2 * C.rC)) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  have h := (p11FastMean_differentiableOn hC).comp
    (f := fun J : P11CVec n => (J, (0 : P11Phase n))) (by fun_prop)
    (fun J hJ => ⟨hJ, by simpa using hrz0⟩)
  exact h.congr fun J hJ => p11C_eq_fastMean hC hJ

/-- The quartic remainder of the fast mean. -/
def p11R4 (C : P11SecularData n) (p : P11CVec n × P11Phase n) : ℂ :=
  p11FastMean C.F p.1 p.2 - C.C p.1 - ∑ i, C.Omega p.1 i * (p.2.1 i ^ 2 + p.2.2 i ^ 2) / 2

/-- The fast-averaging remainder `ε ḡ = G - FastMean`. -/
def p11Gbar (C : P11SecularData n) (Fast : P11FastData n) (p : P11CVec n × P11Phase n) : ℂ :=
  Fast.G p - p11FastMean C.F p.1 p.2

theorem p11G_decomp (C : P11SecularData n) (Fast : P11FastData n) (p : P11CVec n × P11Phase n) :
    Fast.G p = C.C p.1 + ∑ i, C.Omega p.1 i * ((p.2.1 i ^ 2 + p.2.2 i ^ 2) / 2) +
      p11R4 C p + p11Gbar C Fast p := by
  unfold p11R4 p11Gbar
  have : ∑ i, C.Omega p.1 i * (p.2.1 i ^ 2 + p.2.2 i ^ 2) / 2 =
      ∑ i, C.Omega p.1 i * ((p.2.1 i ^ 2 + p.2.2 i ^ 2) / 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

theorem p11R4_differentiableOn (hC : P11SecularSpec D C) :
    DifferentiableOn ℂ (p11R4 C)
      (ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz) := by
  obtain ⟨hOm, -⟩ := secular_extract hC
  have h1 := p11FastMean_differentiableOn hC
  have h2 : DifferentiableOn ℂ (fun p : P11CVec n × P11Phase n => C.C p.1)
      (ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz) :=
    (p11C_differentiableOn hC).comp (f := fun p : P11CVec n × P11Phase n => p.1) (by fun_prop)
      fun p hp => hp.1
  have h3 : DifferentiableOn ℂ (fun p : P11CVec n × P11Phase n =>
      ∑ i, C.Omega p.1 i * (p.2.1 i ^ 2 + p.2.2 i ^ 2) / 2)
      (ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz) := by
    apply DifferentiableOn.fun_sum
    intro i _
    have : DifferentiableOn ℂ (fun p : P11CVec n × P11Phase n => C.Omega p.1 i)
        (ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz) :=
      ((differentiableOn_pi.1 hOm i).comp (f := fun p : P11CVec n × P11Phase n => p.1)
        (by fun_prop) fun p hp => hp.1)
    have h5 : DifferentiableOn ℂ (fun p : P11CVec n × P11Phase n =>
        p.2.1 i ^ 2 + p.2.2 i ^ 2)
        (ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz) := by
      apply Differentiable.differentiableOn
      fun_prop
    have h6 := (this.fun_mul h5).fun_mul (differentiableOn_const (2 : ℂ)⁻¹)
    exact h6.congr fun p _ => by simp only [div_eq_mul_inv]
  exact (h1.sub h2).sub h3

theorem p11R4_bound (hC : P11SecularSpec D C) {J : P11CVec n}
    (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) {z : P11Phase n} (hz : ‖z‖ < C.rz) :
    ‖p11R4 C (J, z)‖ ≤ C.MF / C.rz ^ 4 * ‖z‖ ^ 4 := by
  obtain ⟨-, -, -, hmean, -⟩ := secular_extract hC
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  have := hmean J hJ z hz
  unfold p11R4
  refine this.trans (le_of_eq ?_)
  rw [div_pow]; field_simp

theorem p11R4_jets (hC : P11SecularSpec D C) {J : P11CVec n}
    (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) :
    ∀ j < 4, iteratedFDeriv ℂ j (fun z : P11Phase n => p11R4 C (J, z)) 0 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -⟩ := fast_consts hC
  refine p11_jets_vanish_of_pow_bound hrz0 ?_ fun z hz => p11R4_bound hC hJ (mem_ball_zero_iff.1 hz)
  exact (p11R4_differentiableOn hC).comp (f := fun z : P11Phase n => (J, z)) (by fun_prop)
    fun z hz => ⟨hJ, hz⟩

end Mean

end KAM.Planetary

end
