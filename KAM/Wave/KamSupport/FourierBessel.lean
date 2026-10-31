/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.FourierSeriesVector
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bessel's inequality for Hilbert-valued functions on the torus
(support for blueprint-W `bpW:w1:fourier-l2`, step `stepW:w1:parseval`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

For `g : ℝⁿ → H` continuous, `H` a complex Hilbert space, and `d_k = ∫ e^{-2πik·x} g(x) dx` its
Fourier coefficients (`KAM.torusCoeffW`): for every finite set `K ⊂ ℤⁿ`,
`∑_{k∈K} ‖d_k‖² ≤ ∫ ‖g‖²` (`kamBessel`). The blueprint's Parseval equality in the step is
replaced by this inequality, which is all that is used (the bound `≤ M²`). The proof expands
`0 ≤ ∫ ‖g - ∑_{k∈K} d_k χ_k‖²`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM MeasureTheory
open scoped ComplexConjugate

variable {n : ℕ}

/-- The character `χ_k` on the real torus, `ℂ`-valued. -/
def kamChi (k : Fin n → ℤ) (x : Fin n → ℝ) : ℂ := character k (fun j => (x j : ℂ))

theorem continuous_kamChi (k : Fin n → ℤ) : Continuous (kamChi k) :=
  (differentiable_character k).continuous.comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))

theorem conj_kamChi (k : Fin n → ℤ) (x : Fin n → ℝ) : conj (kamChi k x) = kamChi (-k) x := by
  unfold kamChi character
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, map_intCast, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem kamChi_mul (k l : Fin n → ℤ) (x : Fin n → ℝ) : kamChi k x * kamChi l x = kamChi (k + l) x :=
  character_mul k l _

theorem torusAverage_kamChi (m : Fin n → ℤ) :
    torusAverage (kamChi m) = if m = 0 then 1 else 0 := torusAverage_character m

theorem norm_kamChi (k : Fin n → ℤ) (x : Fin n → ℝ) : ‖kamChi k x‖ = 1 := norm_character_real k x

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trigonometric polynomial `∑_{k∈K} χ_k d_k`. -/
def kamTrigPoly (K : Finset (Fin n → ℤ)) (d : (Fin n → ℤ) → H) (x : Fin n → ℝ) : H :=
  ∑ k ∈ K, kamChi k x • d k

omit [CompleteSpace H] in
theorem continuous_kamTrigPoly (K : Finset (Fin n → ℤ)) (d : (Fin n → ℤ) → H) :
    Continuous (kamTrigPoly K d) :=
  continuous_finsetSum _ fun k _ => (continuous_kamChi k).smul continuous_const

private theorem integrable_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin n → ℝ) → E} (hf : Continuous f) :
    Integrable f (volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
  integrableOn_unitCube_of_continuous hf

theorem kamBessel_cross {g : (Fin n → ℝ) → H} (hg : Continuous g) (K : Finset (Fin n → ℤ))
    (d : (Fin n → ℤ) → H) (hd : ∀ k, d k = torusCoeffW g k) :
    torusAverage (fun x => (inner ℂ (kamTrigPoly K d x) (g x))) =
      ∑ k ∈ K, ((‖d k‖ ^ 2 : ℝ) : ℂ) := by
  have hpt : ∀ x, (inner ℂ (kamTrigPoly K d x) (g x)) =
      ∑ k ∈ K, (inner ℂ (d k) (kamChi (-k) x • g x)) := by
    intro x
    unfold kamTrigPoly
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, inner_smul_right, conj_kamChi]
  simp_rw [hpt]
  unfold torusAverage
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hv : Continuous fun x => kamChi (-k) x • g x := (continuous_kamChi _).smul hg
    have := ((innerSL ℂ (d k)).restrictScalars ℝ).integral_comp_comm (integrable_cube hv)
    simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at this
    rw [this]
    have hk : ∫ x in Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1, kamChi (-k) x • g x =
        d k := by
      rw [hd k]; rfl
    rw [hk, inner_self_eq_norm_sq_to_K]
    simp
  · exact integrable_cube ((continuous_const.inner ((continuous_kamChi _).smul hg)))

omit [CompleteSpace H] in
theorem kamBessel_quad (K : Finset (Fin n → ℤ)) (d : (Fin n → ℤ) → H) :
    torusAverage (fun x => inner ℂ (kamTrigPoly K d x) (kamTrigPoly K d x)) =
      ∑ k ∈ K, ((‖d k‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hpt : ∀ x, inner ℂ (kamTrigPoly K d x) (kamTrigPoly K d x) =
      ∑ k ∈ K, ∑ l ∈ K, kamChi (-k + l) x * inner ℂ (d k) (d l) := by
    intro x
    unfold kamTrigPoly
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, inner_smul_right, conj_kamChi, ← mul_assoc, kamChi_mul]
  simp_rw [hpt]
  unfold torusAverage
  have hint : ∀ k l : Fin n → ℤ, Integrable (fun x => kamChi (-k + l) x * inner ℂ (d k) (d l))
      (volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)) := fun k l =>
    integrable_cube ((continuous_kamChi _).mul continuous_const)
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  have hl : ∀ l ∈ K, ∫ x in Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1,
      kamChi (-k + l) x * inner ℂ (d k) (d l) = if l = k then inner ℂ (d k) (d k) else 0 := by
    intro l _
    rw [integral_mul_const]
    have := torusAverage_kamChi (-k + l)
    unfold torusAverage at this
    rw [this]
    by_cases hlk : l = k
    · subst hlk; simp
    · have : -k + l ≠ 0 := fun h => hlk (by simpa [add_comm, add_eq_zero_iff_eq_neg] using h)
      simp [this, hlk]
  simp only [Finset.sum_congr rfl hl, Finset.sum_ite_eq', hk, ite_true]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Bessel's inequality** for continuous Hilbert-valued functions on the torus: for every finite
`K ⊂ ℤⁿ`, `∑_{k∈K} ‖ĝ_k‖² ≤ ∫ ‖g‖²`. -/
theorem kamBessel {g : (Fin n → ℝ) → H} (hg : Continuous g) (K : Finset (Fin n → ℤ)) :
    ∑ k ∈ K, ‖torusCoeffW g k‖ ^ 2 ≤ torusAverage (fun x => ‖g x‖ ^ 2) := by
  classical
  set d : (Fin n → ℤ) → H := fun k => torusCoeffW g k with hd
  set h := kamTrigPoly K d with hh
  have hhc : Continuous h := continuous_kamTrigPoly K d
  have hB := kamBessel_cross hg K d fun k => rfl
  have hC := kamBessel_quad K d
  set S : ℝ := ∑ k ∈ K, ‖d k‖ ^ 2 with hS
  have hBre : torusAverage (fun x => (inner ℂ (h x) (g x)).re) = S := by
    have := integral_re (μ := volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1))
      (𝕜 := ℂ) (f := fun x => inner ℂ (h x) (g x)) (integrable_cube (hhc.inner hg))
    unfold torusAverage at hB ⊢
    simp only [RCLike.re_to_complex] at this
    rw [this, hB, hS]
    simp [Complex.re_sum, -Complex.ofReal_pow]
  have hCre : torusAverage (fun x => (inner ℂ (h x) (h x)).re) = S := by
    have := integral_re (μ := volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1))
      (𝕜 := ℂ) (f := fun x => inner ℂ (h x) (h x)) (integrable_cube (hhc.inner hhc))
    unfold torusAverage at hC ⊢
    simp only [RCLike.re_to_complex] at this
    rw [this, hC, hS]
    simp [Complex.re_sum, -Complex.ofReal_pow]
  have hpt : ∀ x, ‖g x - h x‖ ^ 2 =
      ‖g x‖ ^ 2 - 2 * (inner ℂ (h x) (g x)).re + (inner ℂ (h x) (h x)).re := by
    intro x
    have hself := inner_self_eq_norm_sq (𝕜 := ℂ) (h x)
    simp only [RCLike.re_to_complex] at hself
    rw [norm_sub_sq (𝕜 := ℂ), inner_re_symm, hself]
    simp only [RCLike.re_to_complex]
  have h0 : 0 ≤ torusAverage (fun x => ‖g x - h x‖ ^ 2) :=
    integral_nonneg fun x => sq_nonneg _
  simp_rw [hpt] at h0
  have i1 : Continuous fun x => ‖g x‖ ^ 2 := hg.norm.pow 2
  have i2 : Continuous fun x => (inner ℂ (h x) (g x)).re :=
    Complex.continuous_re.comp (hhc.inner hg)
  have i3 : Continuous fun x => (inner ℂ (h x) (h x)).re :=
    Complex.continuous_re.comp (hhc.inner hhc)
  unfold torusAverage at h0 hBre hCre ⊢
  have i4 : Continuous fun x => ‖g x‖ ^ 2 - 2 * (inner ℂ (h x) (g x)).re :=
    i1.sub (continuous_const.mul i2)
  have e1 := integral_add (integrable_cube i4) (integrable_cube i3)
  have i5 : Continuous fun x => 2 * (inner ℂ (h x) (g x)).re := continuous_const.mul i2
  have e2 := integral_sub (integrable_cube i1) (integrable_cube i5)
  have e3 := integral_const_mul
    (μ := volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)) (2 : ℝ)
    (fun x => (inner ℂ (h x) (g x)).re)
  rw [e1, e2, e3, hBre, hCre] at h0
  linarith

end Hilbert

end KAM.Wave
