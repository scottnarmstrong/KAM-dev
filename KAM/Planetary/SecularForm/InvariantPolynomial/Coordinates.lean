/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.PlaneDot

/-!
# Invariant polynomials: complex coordinates

First step of the proof of the first fundamental theorem for `O(2)` (`bpP:p8:e-weyl`): the
complex coordinates `z = x + i y`, `w = x - i y` of planar vectors, the substitution `toZW` of a
real polynomial in `(x, y)` into a complex polynomial in `(z, w)`, the rotation by a unit complex
number as a change of the coordinates `(z, w) ↦ (t z, t⁻¹ w)`, and a finite-sum lemma extracting
the balanced part of a Laurent-type polynomial that is constant on the unit circle.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace KAM.Planetary
namespace SecularForm
namespace Weyl

variable {n : ℕ}

theorem infinite_unit_circle : Set.Infinite {t : ℂ | ‖t‖ = 1} := by
  have hinj : Set.InjOn (fun θ : ℝ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)
      (Set.Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    have h1 := Complex.arg_cos_add_sin_mul_I (θ := a)
      ⟨by linarith [ha.1, Real.pi_pos], by linarith [ha.2, Real.pi_gt_three]⟩
    have h2 := Complex.arg_cos_add_sin_mul_I (θ := b)
      ⟨by linarith [hb.1, Real.pi_pos], by linarith [hb.2, Real.pi_gt_three]⟩
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h1 h2
    rw [← h1, ← h2]
    exact congrArg Complex.arg hab
  refine (Set.Ioo_infinite (show (0:ℝ) < 1 by norm_num) |>.image hinj).mono ?_
  rintro _ ⟨θ, _, rfl⟩
  simp [Complex.norm_cos_add_sin_mul_I]

theorem sum_unbalanced_eq_zero {ι : Type*} (s : Finset ι) (a : ι → ℂ) (A B : ι → ℕ) (N : ℕ)
    (hA : ∀ i ∈ s, A i ≤ N) (hB : ∀ i ∈ s, B i ≤ N)
    (h : ∀ t : ℂ, ‖t‖ = 1 → ∑ i ∈ s, a i * t ^ A i * (t⁻¹) ^ B i = ∑ i ∈ s, a i) :
    ∑ i ∈ s with A i ≠ B i, a i = 0 := by
  classical
  set E : ι → ℕ := fun i => A i + (N - B i) with hE
  set S := ∑ i ∈ s, a i with hS
  let G : Polynomial ℂ :=
    ∑ i ∈ s, Polynomial.C (a i) * Polynomial.X ^ E i - Polynomial.C S * Polynomial.X ^ N
  have hG : G = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine infinite_unit_circle.mono ?_
    intro t ht
    have ht1 : ‖t‖ = 1 := ht
    have ht0 : t ≠ 0 := by intro h0; simp [h0] at ht1
    have key := h t ht1
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, G, Polynomial.eval_sub,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    have : ∀ i ∈ s, a i * t ^ E i = t ^ N * (a i * t ^ A i * (t⁻¹) ^ B i) := by
      intro i hi
      have hNB : N = B i + (N - B i) := by have := hB i hi; omega
      have hk : t ^ B i * (t⁻¹) ^ B i = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ ht0, one_pow]
      have hN : t ^ N = t ^ B i * t ^ (N - B i) := by rw [← pow_add, ← hNB]
      simp only [hE]
      rw [hN, pow_add (t) (A i) (N - B i)]
      linear_combination (-(a i * t ^ A i * t ^ (N - B i))) * hk
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, key]
    simp only [hS]
    ring
  have hcoef : ∀ j, ∑ i ∈ s, (if j = E i then a i else 0) = if j = N then S else 0 := by
    intro j
    have := congrArg (fun p : Polynomial ℂ => p.coeff j) hG
    simp only [G, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero] at this
    simp only [mul_ite, mul_one, mul_zero] at this
    exact sub_eq_zero.mp this
  have hsum : ∑ j ∈ (Finset.range (2*N+1)).erase N, ∑ i ∈ s, (if j = E i then a i else 0) =
      ∑ i ∈ s with A i ≠ B i, a i := by
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := hA i hi
    have h2 := hB i hi
    rw [Finset.sum_ite_eq']
    by_cases hAB : A i = B i
    · have : E i = N := by simp only [hE]; omega
      simp [this, hAB]
    · have : E i ∈ (Finset.range (2*N+1)).erase N := by
        simp only [Finset.mem_erase, Finset.mem_range, hE]; omega
      simp [this, hAB]
  rw [← hsum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hcoef j]
  simp [Finset.ne_of_mem_erase hj]

/-- Complex coordinates `z = x + i y` (tag `true`) and `w = x - i y` (tag `false`). -/
def zw (u : Fin n → Fin 2 → ℝ) : Fin n × Bool → ℂ := fun kb =>
  if kb.2 then (u kb.1 0 : ℂ) + Complex.I * (u kb.1 1 : ℂ)
  else (u kb.1 0 : ℂ) - Complex.I * (u kb.1 1 : ℂ)

def toZW : MvPolynomial (Fin n × Fin 2) ℝ →+* MvPolynomial (Fin n × Bool) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap ℝ ℂ)) (fun ic =>
    if ic.2 = 0 then C (1/2 : ℂ) * (X (ic.1, true) + X (ic.1, false))
    else C (-Complex.I/2) * (X (ic.1, true) - X (ic.1, false)))

theorem eval_toZW (P : MvPolynomial (Fin n × Fin 2) ℝ) (u : Fin n → Fin 2 → ℝ) :
    MvPolynomial.eval (zw u) (toZW P) =
      ((MvPolynomial.eval (fun ic => u ic.1 ic.2) P : ℝ) : ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [toZW]
  | add p q hp hq => simp [hp, hq]
  | mul_X p ic hp =>
    obtain ⟨k, c⟩ := ic
    simp only [map_mul, hp, eval_X, Complex.ofReal_mul]
    congr 1
    fin_cases c
    · simp [toZW, zw]; ring
    · simp [toZW, zw]; ring_nf; simp [Complex.I_sq]

def rotMat (t : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![t.re, -t.im; t.im, t.re]

theorem rotMat_orth {t : ℂ} (ht : ‖t‖ = 1) : (rotMat t).transpose * rotMat t = 1 := by
  have h : t.re ^ 2 + t.im ^ 2 = 1 := by
    have := Complex.sq_norm t
    rw [Complex.normSq_apply, ht] at this
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

theorem zw_rot (t : ℂ) (u : Fin n → Fin 2 → ℝ) (kb : Fin n × Bool) :
    zw (fun k => (rotMat t).mulVec (u k)) kb =
      if kb.2 then t * zw u kb else (starRingEnd ℂ t) * zw u kb := by
  obtain ⟨k, b⟩ := kb
  cases b <;>
    simp [zw, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff] <;>
    constructor <;> ring

end Weyl
end SecularForm
end KAM.Planetary
