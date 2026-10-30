/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.FourierBessel
public import KAM.Wave.KamSupport.FourierShift
public import KAM.Wave.KamSupport.FourierBanach

/-!
# Hilbert-valued Fourier series on strips (blueprint-W `bpW:w1:fourier-l2`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

For `H` a complex Hilbert space and `u : T_s → H` holomorphic, `1`-periodic, `‖u‖ ≤ M`:

* (i) `kamFourierL2_sum_le`: `∑_k ‖û_k‖² e^{4π|k|₁ s} ≤ 2ⁿ M²`. The Parseval step is replaced by
  Bessel's inequality (`kamBessel`), which suffices for the upper bound; the shifted coefficients are
  `kamFourier_shift`; the orthant step sums over the `2ⁿ` sign vectors.
* (ii) `kamFourierL2_summation`: the summation lemma, an instance of
  `kamFourierBanach_summation`.
* (iii) `kamFourierL2_eq_fourierSum`: `u` is the sum of its Fourier series on `T_s` (in particular on
  `T_{s'}`, `s' < s`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM MeasureTheory Filter
open scoped Topology

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orthant vector `η_ε = -s' ε`, `ε ∈ {±1}ⁿ` encoded by `Bool`. -/
def kamOrthant (s' : ℝ) (ε : Fin n → Bool) (j : Fin n) : ℝ := if ε j then -s' else s'

theorem abs_kamOrthant {s' : ℝ} (hs' : 0 ≤ s') (ε : Fin n → Bool) (j : Fin n) :
    |kamOrthant s' ε j| = s' := by
  unfold kamOrthant; split_ifs <;> simp [abs_of_nonneg hs']

/-- For each `k`, some orthant has `-η_ε · k = s' |k|₁`. -/
theorem exists_kamOrthant_eq (s' : ℝ) (k : Fin n → ℤ) :
    ∃ ε : Fin n → Bool, -(∑ j, (k j : ℝ) * kamOrthant s' ε j) = s' * Fourier.modeSize k := by
  refine ⟨fun j => decide (0 ≤ k j), ?_⟩
  rw [Fourier.modeSize, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold kamOrthant
  by_cases h : 0 ≤ k j
  · have h' : (0 : ℝ) ≤ k j := by exact_mod_cast h
    simp [h, abs_of_nonneg h']
    ring
  · have h' : (k j : ℝ) < 0 := by exact_mod_cast not_le.mp h
    simp [h, abs_of_neg h']
    ring

/-- One orthant: `∑_{k∈K} ‖û_k‖² e^{-4π k·η} ≤ M²`, via the shifted coefficients and Bessel. -/
theorem kamFourierL2_orthant_le {s M : ℝ} (hs : 0 < s) {u : (Fin n → ℂ) → H}
    (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) {η : Fin n → ℝ} (hη : ∀ i, |η i| < s)
    (K : Finset (Fin n → ℤ)) :
    ∑ k ∈ K, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (-(2 * (2 * Real.pi * ∑ j, (k j : ℝ) * η j))) ≤ M ^ 2 := by
  set g : (Fin n → ℝ) → H := fun x => u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I)
    with hg
  have hmem : ∀ x : Fin n → ℝ,
      ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I) ∈ complexStrip n s := by
    intro x j
    have him : (((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I) j).im = η j := by
      simp [Complex.mul_im]
    rw [him]; exact hη j
  have hgc : Continuous g :=
    hu.continuousOn.comp_continuous
      ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).add
        continuous_const) hmem
  have hB := kamBessel hgc K
  have hnorm : torusAverage (fun x => ‖g x‖ ^ 2) ≤ M ^ 2 := by
    refine le_trans (le_abs_self _) ?_
    have := norm_torusAverage_le (n := n) (f := fun x => ‖g x‖ ^ 2) (A := M ^ 2) (fun x _ => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hM _ (hmem x)) 2)
    simpa using this
  refine le_trans (le_of_eq ?_) (hB.trans hnorm)
  refine Finset.sum_congr rfl fun k _ => ?_
  have hshift := kamFourier_shift hs hu hp hη k
  have hcoef : torusCoeffW g k = ((Real.exp (-(2 * Real.pi * ∑ j, (k j : ℝ) * η j)) : ℝ) : ℂ) •
      torusCoeffW (fun x => u fun j => (x j : ℂ)) k := hshift
  rw [hcoef, norm_smul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring_nf

/-- Finite sums at a smaller width: for `0 ≤ s' < s`,
`∑_{k∈K} ‖û_k‖² e^{4π s'|k|₁} ≤ 2ⁿ M²` (the orthant step). -/
theorem kamFourierL2_finite_le_of_lt {s s' M : ℝ} (hs : 0 < s) (hs'0 : 0 ≤ s') (hs's : s' < s)
    {u : (Fin n → ℂ) → H} (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) (K : Finset (Fin n → ℤ)) :
    ∑ k ∈ K, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (4 * Real.pi * s' * Fourier.modeSize k) ≤ 2 ^ n * M ^ 2 := by
  classical
  have horth : ∀ ε : Fin n → Bool,
      ∑ k ∈ K, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (-(2 * (2 * Real.pi * ∑ j, (k j : ℝ) * kamOrthant s' ε j))) ≤ M ^ 2 :=
    fun ε => kamFourierL2_orthant_le hs hu hp hM
      (fun i => by rw [abs_kamOrthant hs'0]; exact hs's) K
  have hsum : ∑ ε : Fin n → Bool, ∑ k ∈ K, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (-(2 * (2 * Real.pi * ∑ j, (k j : ℝ) * kamOrthant s' ε j))) ≤ 2 ^ n * M ^ 2 := by
    calc _ ≤ ∑ _ε : Fin n → Bool, M ^ 2 := Finset.sum_le_sum fun ε _ => horth ε
      _ = 2 ^ n * M ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
        norm_num
  refine le_trans ?_ hsum
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  obtain ⟨ε₀, hε₀⟩ := exists_kamOrthant_eq s' k
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ε : Fin n → Bool =>
    Real.exp (-(2 * (2 * Real.pi * ∑ j, (k j : ℝ) * kamOrthant s' ε j))))
    (fun ε _ => (Real.exp_pos _).le) (Finset.mem_univ ε₀))
  congr 1
  have : 2 * (2 * Real.pi * ∑ j, (k j : ℝ) * kamOrthant s' ε₀ j) =
      -(4 * Real.pi * (-(∑ j, (k j : ℝ) * kamOrthant s' ε₀ j))) := by ring
  rw [this, neg_neg, hε₀]
  ring

/-- **Hilbert-valued Fourier coefficients on strips** (blueprint `bpW:w1:fourier-l2` (i)):
`∑_k ‖û_k‖² e^{4π|k|₁ s} ≤ 2ⁿ M²`, and the series converges. -/
theorem kamFourierL2_sum_le {s M : ℝ} (hs : 0 < s) {u : (Fin n → ℂ) → H}
    (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) :
    Summable (fun k => ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (4 * Real.pi * s * Fourier.modeSize k)) ∧
      ∑' k, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
          Real.exp (4 * Real.pi * s * Fourier.modeSize k) ≤ 2 ^ n * M ^ 2 := by
  have hfin : ∀ K : Finset (Fin n → ℤ),
      ∑ k ∈ K, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (4 * Real.pi * s * Fourier.modeSize k) ≤ 2 ^ n * M ^ 2 := by
    intro K
    have hc : Continuous fun r : ℝ => ∑ k ∈ K,
        ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
          Real.exp (4 * Real.pi * r * Fourier.modeSize k) := by fun_prop
    have hlim := (hc.tendsto s).mono_left (nhdsWithin_le_nhds (s := Set.Iio s))
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hs] with r hr
    exact kamFourierL2_finite_le_of_lt hs hr.1.le hr.2 hu hp hM K
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (4 * Real.pi * s * Fourier.modeSize k) := fun k => by positivity
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

/-- **Summation** (blueprint `bpW:w1:fourier-l2` (ii)): the Hilbert space is a Banach space, so the
summation lemma of `bpW:w1:fourier-banach` (iii) applies (with `ρ = s`). -/
theorem kamFourierL2_summation {ρ : ℝ} (hρ : 0 < ρ) {a : (Fin n → ℤ) → H}
    (ha : Summable fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) :
    DifferentiableOn ℂ (fourierSumVec a) (complexStrip n ρ) ∧
    (∀ (i : Fin n) z, z ∈ complexStrip n ρ →
      fourierSumVec a (z + Pi.single i 1) = fourierSumVec a z) ∧
    (∀ θ ∈ complexStrip n ρ,
      ‖fourierSumVec a θ‖ ≤ ∑' k, ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) ∧
    (∀ k, torusCoeffW (fun x => fourierSumVec a fun j => (x j : ℂ)) k = a k) := by
  obtain ⟨-, -, hb, hd, hper, hc⟩ := kamFourierBanach_summation hρ ha
  exact ⟨hd, hper, hb, hc⟩

/-- **Representation** (blueprint `bpW:w1:fourier-l2` (iii)): `u` is the sum of its Fourier series
on `T_s`, hence on `T_{s'}`, `s' < s`. -/
theorem kamFourierL2_eq_fourierSum {s M : ℝ} (hs : 0 < s) {u : (Fin n → ℂ) → H}
    (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n s) :
    u θ = fourierSumVec (torusCoeffW fun x => u fun j => (x j : ℂ)) θ :=
  eq_fourierSumVec_torusCoeffW hs hu hp hM hθ

end KAM.Wave
