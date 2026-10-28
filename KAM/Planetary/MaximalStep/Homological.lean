/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.FourierSeriesVector
public import KAM.Weighted.Projections
public import KAM.Weighted.Parametric
public import KAM.Planetary.MaximalStep.Constants
public import KAM.Planetary.MaximalStep.Parameter

/-!
# Maximal homological equation (P11A-C5, `bpP:p11a:homological-maximal`)

The solution `p11Solve T w P` of `ω(b)·∂_θ φ = P - ⟨P⟩` is the explicit finite trigonometric sum
`∑_{0<|k|₁≤T} P̂_k(b) / (2πi k·ω(b)) χ_k(θ)`. Here `hmCoef` is its coefficient family and
`hmCut` the coefficient family of the truncated datum; every statement is read off from the finite
Fourier sums (`stepP:p11a:hm-coeff`, `hm-a`, `hm-bc`, `hm-d`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- The generator is defined from existing scalar truncation; no Diophantine premise. -/
def p11Solve {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n)
    (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) : ℂ :=
  ∑' k : Fin n → ℤ, if k=0 ∨ T < KAM.Fourier.modeSize k then 0 else
    KAM.Weighted.coeff P b k / (2*Real.pi*Complex.I*p11dotC k (w b)) * KAM.character k theta
def p11AngleClass {n : ℕ} (r : ℝ) (B : Set (P11CVec n))
    (P : P11CVec n × P11CVec n → ℂ) : Prop :=
  DifferentiableOn ℂ P (KAM.complexStrip n r ×ˢ B) ∧
    ∀ j : Fin n, ∀ z ∈ KAM.complexStrip n r ×ˢ B, P (z.1+Pi.single j 1,z.2)=P z
def p11AngleAverage {n : ℕ} (P : P11CVec n × P11CVec n → ℂ) (b : P11CVec n) : ℂ :=
  KAM.Weighted.coeff P b 0

/-! ### Finite trigonometric sums -/

/-- The coefficients of `p11Solve T w P ·  b`. -/
def hmCoef {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n) (P : P11CVec n × P11CVec n → ℂ)
    (b : P11CVec n) (k : Fin n → ℤ) : ℂ :=
  if k=0 ∨ T < KAM.Fourier.modeSize k then 0 else
    KAM.Weighted.coeff P b k / (2*Real.pi*Complex.I*p11dotC k (w b))

/-- The coefficients of the truncation `T_T P`. -/
def hmCut {n : ℕ} (T : ℝ) (P : P11CVec n × P11CVec n → ℂ) (b : P11CVec n)
    (k : Fin n → ℤ) : ℂ :=
  if KAM.Fourier.modeSize k ≤ T then KAM.Weighted.coeff P b k else 0

/-- The finite set of modes `|k|₁ ≤ T`. -/
def hmModes (n : ℕ) (T : ℝ) : Finset (Fin n → ℤ) := KAM.modeCutoff n ⌈T⌉₊

theorem mem_hmModes {n : ℕ} {T : ℝ} {k : Fin n → ℤ} :
    k ∈ hmModes n T ↔ KAM.Fourier.modeSize k ≤ ⌈T⌉₊ := KAM.mem_modeCutoff

theorem mem_hmModes_of_le {n : ℕ} {T : ℝ} {k : Fin n → ℤ} (h : KAM.Fourier.modeSize k ≤ T) :
    k ∈ hmModes n T := mem_hmModes.2 (h.trans (Nat.le_ceil T))

theorem p11Solve_eq {n : ℕ} (T : ℝ) (w : P11CVec n → P11CVec n)
    (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) :
    p11Solve T w P theta b = KAM.fourierSum (hmCoef T w P b) theta := by
  unfold p11Solve KAM.fourierSum hmCoef
  refine tsum_congr fun k => ?_
  split_ifs <;> simp

theorem truncate_eq {n : ℕ} (T : ℝ) (P : P11CVec n × P11CVec n → ℂ) (theta b : P11CVec n) :
    KAM.Weighted.truncate T P (theta, b) = KAM.fourierSum (hmCut T P b) theta := by
  unfold KAM.Weighted.truncate KAM.Weighted.projMode KAM.fourierSum hmCut
  refine tsum_congr fun k => ?_
  by_cases h : KAM.Fourier.modeSize k ≤ T <;> simp [Set.indicator, h]

theorem hmCoef_eq_zero {n : ℕ} {T : ℝ} {w : P11CVec n → P11CVec n}
    {P : P11CVec n × P11CVec n → ℂ} {b : P11CVec n} {k : Fin n → ℤ}
    (h : k ∉ hmModes n T) : hmCoef T w P b k = 0 := by
  have : T < KAM.Fourier.modeSize k := by
    by_contra hc
    exact h (mem_hmModes_of_le (not_lt.1 hc))
  simp [hmCoef, this]

theorem hmCut_eq_zero {n : ℕ} {T : ℝ} {P : P11CVec n × P11CVec n → ℂ} {b : P11CVec n}
    {k : Fin n → ℤ} (h : k ∉ hmModes n T) : hmCut T P b k = 0 := by
  have : ¬ KAM.Fourier.modeSize k ≤ T := fun hc => h (mem_hmModes_of_le hc)
  simp [hmCut, this]

/-- A finitely supported coefficient family. -/
theorem fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (theta : Fin n → ℂ) :
    KAM.fourierSum a theta = ∑ k ∈ S, a k * KAM.character k theta :=
  tsum_eq_sum fun k hk => by simp [hS k hk]

theorem summableWeighted_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (s : ℝ) : KAM.Fourier.SummableWeighted s a :=
  summable_of_ne_finset_zero (s := S) fun k hk => by simp [hS k hk]

theorem torusCoeff_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (k : Fin n → ℤ) :
    KAM.torusCoeff (fun x => KAM.fourierSum a (fun j => (x j : ℂ))) k = a k :=
  KAM.torusCoeff_fourierSum (le_refl 0) (by simpa using summableWeighted_finset hS _) k

theorem hasFDerivAt_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (theta : Fin n → ℂ) :
    HasFDerivAt (KAM.fourierSum a)
      (∑ k ∈ S, a k • (KAM.character k theta • ((2*Real.pi*Complex.I : ℂ) • KAM.modeForm k)))
      theta := by
  have hfun : KAM.fourierSum a = fun x => ∑ k ∈ S, a k * KAM.character k x := by
    funext x; exact fourierSum_finset hS x
  rw [hfun]
  refine HasFDerivAt.fun_sum fun k _ => ?_
  exact ((KAM.hasFDerivAt_character k theta).const_mul (a k))

theorem fderiv_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) (theta v : Fin n → ℂ) :
    fderiv ℂ (KAM.fourierSum a) theta v =
      ∑ k ∈ S, a k * (2*Real.pi*Complex.I*p11dotC k v) * KAM.character k theta := by
  rw [(hasFDerivAt_fourierSum_finset hS theta).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    KAM.modeForm_apply, p11dotC]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem differentiable_fourierSum_finset {n : ℕ} {a : (Fin n → ℤ) → ℂ} {S : Finset (Fin n → ℤ)}
    (hS : ∀ k ∉ S, a k = 0) : Differentiable ℂ (KAM.fourierSum a) := fun theta =>
  (hasFDerivAt_fourierSum_finset hS theta).differentiableAt

end KAM.Planetary
