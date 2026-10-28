/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Fourier.ExpSums
public import KAM.Weighted.Norm
public import KAM.Planetary.MaximalStep.Basic

/-!
# Maximal canonical step: constants (P11A-C0)

The Fourier-cutoff constants `p11C`, `p11Error`, `p11Loss` and the homological constant
`p11Lambda n delta = coth(pi delta)^n - 1` (`bpP:p11a:sec-hom#lambda`), with `p11_lambda_spec`: its
lattice identity `∑_{k≠0} exp(-2 pi delta |k|₁) = p11Lambda n delta` and both upper bounds.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

def p11C (n : ℕ) : ℝ :=
  2*(1+1/Real.pi)*(3*n/(Real.exp 1*Real.pi))^(n-1)

def p11Error (n : ℕ) (T d : ℝ) : ℝ := p11C n*(1+(d^n)⁻¹)*Real.exp (-Real.pi*T*d)

def p11Loss (n : ℕ) (T alpha : ℝ) : ℝ :=
  (Real.log (2*p11C n/alpha)+n*Real.log (Real.pi*T))/(Real.pi*T)

def p11Lambda (n : ℕ) (delta : ℝ) : ℝ := KAM.Weighted.coth (Real.pi*delta)^n-1

/-- lambda definition, its lattice identity and both bounds are separate from the cohomological
theorem. -/
theorem p11_lambda_spec {n : ℕ} (hn : 1 ≤ n) {delta : ℝ} (hd : 0 < delta) :
    Summable (fun k : {k : Fin n → ℤ // k ≠ 0} =>
      Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k.val)) ∧
    (∑' k : {k : Fin n → ℤ // k ≠ 0}, Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k.val))=
      p11Lambda n delta ∧
    p11Lambda n delta ≤ (1+1/(Real.pi*delta))^n-1 ∧
    p11Lambda n delta ≤ (4*n/(Real.pi*delta))^n := by
  have hx : 0 < 2*Real.pi*delta := by positivity
  obtain ⟨hs, hb⟩ := (KAM.Fourier.exp_sums n).2.1 _ hx
  have hh : 2*Real.pi*delta/2 = Real.pi*delta := by ring
  rw [hh] at hs hb
  have hsum : Summable (fun k : Fin n → ℤ =>
      Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k)) := hs.summable
  have hnz : Summable (fun k : {k : Fin n → ℤ // k ≠ 0} =>
      Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k.val)) := hsum.subtype _
  have htsum : (∑' k : {k : Fin n → ℤ // k ≠ 0},
      Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k.val)) = p11Lambda n delta := by
    have h0 := hsum.tsum_eq_add_tsum_ite 0
    have h1 : (∑' k : Fin n → ℤ, if k = 0 then 0 else
        Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k)) =
        ∑' k : {k : Fin n → ℤ // k ≠ 0},
          Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k.val) := by
      refine Eq.trans ?_ (tsum_subtype {k : Fin n → ℤ | k ≠ 0}
        (fun k => Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k))).symm
      refine tsum_congr fun k => ?_
      by_cases hk : k = 0 <;> simp [hk, Set.indicator]
    have hz : KAM.Fourier.modeSize (0 : Fin n → ℤ) = 0 := by simp [KAM.Fourier.modeSize]
    rw [hs.tsum_eq, hz] at h0
    unfold p11Lambda KAM.Weighted.coth
    rw [mul_zero, Real.exp_zero] at h0
    rw [h1] at h0
    linarith
  have e : ∀ k : {k : Fin n → ℤ // k ≠ 0},
      Real.exp (-2*Real.pi*delta*KAM.Fourier.modeSize k.val) =
        Real.exp (-(2*Real.pi*delta)*KAM.Fourier.modeSize k.val) := fun k => by ring_nf
  simp only [e]
  refine ⟨hnz, htsum, ?_, ?_⟩
  · unfold p11Lambda KAM.Weighted.coth
    have hp : 0 ≤ Real.cosh (Real.pi*delta) / Real.sinh (Real.pi*delta) :=
      div_nonneg (Real.cosh_pos _).le (Real.sinh_pos_iff.2 (by positivity)).le
    have : 1 + 2/(2*Real.pi*delta) = 1 + 1/(Real.pi*delta) := by field_simp
    rw [this] at hb
    have := pow_le_pow_left₀ hp hb n
    linarith
  · rw [← htsum]
    have h3 := (KAM.Fourier.exp_sums n).2.2 _ hx
    have : 8*(n:ℝ)/(2*Real.pi*delta) = 4*n/(Real.pi*delta) := by field_simp; ring
    rwa [this] at h3
