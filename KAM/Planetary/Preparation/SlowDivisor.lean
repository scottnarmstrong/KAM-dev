/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowDerivative
public import KAM.Planetary.Preparation.FastDivisor

/-!
# Slow averaging: the divisor clause (P11A-P7c, `stepP:p11:as-nr`)

The pure-slow and mixed divisor bounds `(B1)` for `h₀ = C.h ∘ J + ε W` on the box `V₂`:
the mixed case via `fast_divisor`, the pure-slow case via the Diophantine bound on the secular
frequency `Ω/(2π)` and the `ρ`-derivative bound of `Z`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section SlowDivisor

variable {n : ℕ}

open KAM.NormalForm

/-- The secular frequency `Ω/(2π)` is `L`-Lipschitz on the ball `2 r_C`. -/
theorem Omega_lipschitz {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {J : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) :
    ‖(2 * Real.pi : ℂ)⁻¹ • C.Omega J - (2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0)‖ ≤
      C.L * ‖J - KAM.realInclusion n C.J0‖ := by
  obtain ⟨-, -, ⟨hωd, hΩd⟩, -, -, -, hL, -, -, -, -, hrC0, -⟩ := hC
  have hopen : IsOpen (ball (KAM.realInclusion n C.J0) (2 * C.rC)) := isOpen_ball
  have hd : ∀ x ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC),
      DifferentiableAt ℂ (fun J => (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) :
        Fin (n + n) → ℂ)) x := fun x hx =>
    differentiableAt_append (hωd.differentiableAt (hopen.mem_nhds hx))
      (DifferentiableAt.const_smul (hΩd.differentiableAt (hopen.mem_nhds hx)) ((2 * Real.pi : ℂ)⁻¹))
  have hb : ∀ x ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC),
      ‖fderiv ℂ (fun J => (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) :
        Fin (n + n) → ℂ)) x‖ ≤ C.L := fun x hx => by
    have := hL x hx 1 (Nat.le_add_left 1 _)
    simpa using this
  have hmvt := (convex_ball (KAM.realInclusion n C.J0)
    (2 * C.rC)).norm_image_sub_le_of_norm_fderiv_le
    hd hb (mem_ball_self (by linarith)) hJ
  refine le_trans ?_ hmvt
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => ?_
  have := norm_le_pi_norm (Fin.append (C.omega J) ((2 * Real.pi : ℂ)⁻¹ • C.Omega J) -
    Fin.append (C.omega (KAM.realInclusion n C.J0))
      ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))) (Fin.natAdd n i)
  simpa using this

/-- The real part of `k₂ · Ω(J₀)/(2π)` is `k₂ · ϖ`'s slow block, so it is Diophantine. -/
theorem re_dotC_Omega {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {k : Fin n → ℤ} (hk : k ≠ 0) :
    C.gamma / (KAM.Fourier.modeSize k) ^ C.tau ≤
      |(dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))).re| := by
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, hdio, hrC0, -⟩ := hC
  have hmem : KAM.realInclusion n C.J0 ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    mem_ball_self (by linarith)
  obtain ⟨-, -, hre⟩ := hA C.J0 hmem
  have hk' : (Fin.append (0 : Fin n → ℤ) k : Fin (n + n) → ℤ) ≠ 0 := by
    intro h
    apply hk
    funext i
    have := congrFun h (Fin.natAdd n i)
    simpa using this
  have h := hdio _ hk'
  have e1 : ∑ i : Fin (n + n), |((Fin.append (0 : Fin n → ℤ) k i : ℤ) : ℝ)| =
      KAM.Fourier.modeSize k := by
    rw [Fin.sum_univ_add]
    simp [KAM.Fourier.modeSize]
  have e2 : ∑ i : Fin (n + n), ((Fin.append (0 : Fin n → ℤ) k i : ℤ) : ℝ) *
      (p11PatchData D).varpi C.J0 i =
        (dotC k ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))).re := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, zero_add, dotC, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hr := hre i
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : ((2 * Real.pi : ℂ)⁻¹ * C.Omega (KAM.realInclusion n C.J0) i).re =
        (p11PatchData D).varpi C.J0 (Fin.natAdd n i) := by
      have h1 : ((2 * Real.pi : ℂ)⁻¹) = ((2 * Real.pi)⁻¹ : ℝ) := by push_cast; rfl
      rw [h1, Complex.re_ofReal_mul, hr]
      field_simp
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, this]
  rw [e1, e2] at h
  exact h

end SlowDivisor

end KAM.Planetary

end
