/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# Fast averaging: the divisor bound (P11A-P5, `stepP:p11:af-o1`)

For `J` in the polydisc of radius `s₁` around `J₀` and `0 < |k|₁ ≤ K₁`:
`|k·ω(J)| ≥ |k·ω(J₀)| - |k|₁ |ω(J) - ω(J₀)| ≥ γ K₁^{-τ} - K₁ L s₁ ≥ (3/4) γ K₁^{-τ} ≥ α₁`.
The frequency `ω` is Lipschitz with constant `L` on the ball by the mean value inequality
(`ext-mvt`), and `k·ω(J₀)` has real part `k·ϖ_{J₀}`, which is bounded below by the Diophantine
condition.
-/

@[expose] public noncomputable section
open Set Metric
namespace KAM.Planetary

open KAM.NormalForm

variable {n : ℕ}

theorem differentiableAt_append {a b : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → Fin a → ℂ} {v : E → Fin b → ℂ} {x : E} (hu : DifferentiableAt ℂ u x)
    (hv : DifferentiableAt ℂ v x) :
    DifferentiableAt ℂ (fun y => Fin.append (u y) (v y)) x := by
  rw [differentiableAt_pi]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using differentiableAt_pi.1 hu j
  · simpa only [Fin.append_right] using differentiableAt_pi.1 hv j

/-- The frequency is `L`-Lipschitz on the ball `2 r_C`, from the first derivative of the joint
frequency vector. -/
theorem omega_lipschitz {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {J : P11CVec n} (hJ : J ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC)) :
    ‖C.omega J - C.omega (KAM.realInclusion n C.J0)‖ ≤ C.L * ‖J - KAM.realInclusion n C.J0‖ := by
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
      ((2 * Real.pi : ℂ)⁻¹ • C.Omega (KAM.realInclusion n C.J0))) (Fin.castAdd n i)
  simpa using this

/-- `|k·v| ≤ |k|₁ ‖v‖`. -/
theorem p11_norm_dotC_le (k : Fin n → ℤ) (v : P11CVec n) :
    ‖dotC k v‖ ≤ KAM.Fourier.modeSize k * ‖v‖ := by
  unfold dotC KAM.Fourier.modeSize
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_intCast]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

/-- The real part of `k·ω(J₀)` is `k·ϖ_{J₀}`, so it obeys the Diophantine bound. -/
theorem re_dotC_omega {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {k : Fin n → ℤ} (hk : k ≠ 0) :
    C.gamma / (KAM.Fourier.modeSize k) ^ C.tau ≤
      |(dotC k (C.omega (KAM.realInclusion n C.J0))).re| := by
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, hdio, hrC0, -⟩ := hC
  have hmem : KAM.realInclusion n C.J0 ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    mem_ball_self (by linarith)
  obtain ⟨-, hre, -⟩ := hA C.J0 hmem
  have hk' : (Fin.append k (0 : Fin n → ℤ) : Fin (n + n) → ℤ) ≠ 0 := by
    intro h
    apply hk
    funext i
    have := congrFun h (Fin.castAdd n i)
    simpa using this
  have h := hdio _ hk'
  have e1 : ∑ i : Fin (n + n), |((Fin.append k (0 : Fin n → ℤ) i : ℤ) : ℝ)| =
      KAM.Fourier.modeSize k := by
    rw [Fin.sum_univ_add]
    simp [KAM.Fourier.modeSize]
  have e2 : ∑ i : Fin (n + n), ((Fin.append k (0 : Fin n → ℤ) i : ℤ) : ℝ) *
      (p11PatchData D).varpi C.J0 i = (dotC k (C.omega (KAM.realInclusion n C.J0))).re := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, add_zero, dotC, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hre i]
    simp [Complex.mul_re]
  rw [e1, e2] at h
  exact h

/-- `stepP:p11:af-o1`: the divisor bound `α ≤ |k·ω(J)|` on the polydisc of radius `s₁`. -/
theorem fast_divisor {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {s1 K α : ℝ} (hs1 : s1 ≤ C.rC) (hK : 0 < K)
    (hsK : K * C.L * s1 ≤ C.gamma * K ^ (-C.tau) / 4)
    (hα : α ≤ 3 / 4 * C.gamma * K ^ (-C.tau)) :
    DivisorBound (KAM.actionNbhd {C.J0} s1) K {0} C.h α := by
  intro I hI k hk
  obtain ⟨hkK, hk0⟩ := hk
  have hk0' : k ≠ 0 := fun h => hk0 (by simpa using h)
  have hC' := hC
  obtain ⟨-, -, -, hτ, -, hωh, -, -, hγ0, -, -, hrC0, -⟩ := hC
  obtain ⟨J, hJ, hIJ⟩ := hI
  have hJ0 : J = C.J0 := hJ
  subst hJ0
  have hIJ' : ‖I - KAM.realInclusion n C.J0‖ < s1 := by
    have : KAM.realInclusion n C.J0 = fun i => (C.J0 i : ℂ) := by funext i; simp
    rw [this]; exact hIJ
  have hIm : I ∈ ball (KAM.realInclusion n C.J0) (2 * C.rC) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hfreq : freq C.h I = C.omega I := by
    rw [hωh I hIm]; rfl
  rw [hfreq]
  have hlip := omega_lipschitz hC' hIm
  have hms := p11_norm_dotC_le k (C.omega I - C.omega (KAM.realInclusion n C.J0))
  have hdio := re_dotC_omega hC' hk0'
  have hsub : dotC k (C.omega I) = dotC k (C.omega (KAM.realInclusion n C.J0)) +
      dotC k (C.omega I - C.omega (KAM.realInclusion n C.J0)) := by
    unfold dotC
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]; ring
  have hpos : 0 < KAM.Fourier.modeSize k := by
    unfold KAM.Fourier.modeSize
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hk0'
    exact lt_of_lt_of_le (abs_pos.2 (by exact_mod_cast hi))
      (Finset.single_le_sum (f := fun j => |(k j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hτ0 : 0 < C.tau := by
    rw [hτ]
    exact lt_max_of_lt_right (by have := (show (2 : ℕ) ≤ n from D.n_ge); positivity)
  have hdiv1 : C.gamma * K ^ (-C.tau) ≤ C.gamma / (KAM.Fourier.modeSize k) ^ C.tau := by
    rw [Real.rpow_neg hK.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hγ0.le (Real.rpow_pos_of_pos hpos _)
      (Real.rpow_le_rpow hpos.le hkK hτ0.le)
  have hre : |(dotC k (C.omega (KAM.realInclusion n C.J0))).re| ≤
      ‖dotC k (C.omega (KAM.realInclusion n C.J0))‖ := Complex.abs_re_le_norm _
  have hKL : KAM.Fourier.modeSize k * (C.L * ‖I - KAM.realInclusion n C.J0‖) ≤ K * C.L * s1 := by
    have hL0 : 0 ≤ C.L := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL1, -⟩ := hC'
      linarith
    calc _ ≤ K * (C.L * s1) :=
          mul_le_mul hkK (mul_le_mul_of_nonneg_left hIJ'.le hL0) (by positivity) hK.le
      _ = _ := by ring
  have hmul : KAM.Fourier.modeSize k * ‖C.omega I - C.omega (KAM.realInclusion n C.J0)‖ ≤
      KAM.Fourier.modeSize k * (C.L * ‖I - KAM.realInclusion n C.J0‖) :=
    mul_le_mul_of_nonneg_left hlip hpos.le
  have htri : ‖dotC k (C.omega (KAM.realInclusion n C.J0))‖ - ‖dotC k (C.omega I -
      C.omega (KAM.realInclusion n C.J0))‖ ≤ ‖dotC k (C.omega I)‖ := by
    rw [hsub]
    have := norm_sub_norm_le (dotC k (C.omega (KAM.realInclusion n C.J0))) (-(dotC k (C.omega I -
      C.omega (KAM.realInclusion n C.J0))))
    rw [norm_neg] at this
    simpa using this
  linarith

end KAM.Planetary

end
