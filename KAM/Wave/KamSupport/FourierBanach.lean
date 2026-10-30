/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.Lattice
public import KAM.Strip.FourierSeriesVector

/-!
# Banach-valued Fourier coefficients on strips (blueprint-W `bpW:w1:fourier-banach`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.
(Replaces the false operator-valued square-sum bound of P96-K p. 127, erratum E-W-Pos96K-1.)

Let `F` be a complex Banach space, `u : T_s → F` holomorphic, `1`-periodic, `‖u‖ ≤ M`. The
`F`-valued coefficient is track K's `KAM.torusCoeffW` (the Bochner average of `e^{-2πik·x} u(x)`).

* (i) `kamFourierBanach_coeff_le`: `‖û_k‖ ≤ M e^{-2π|k|₁ s}`;
* (ii) `kamFourierBanach_sum_le`, `kamFourierBanach_weighted_sum_le`: the sums against
  `e^{2π|k|₁(s-σ)}` and `(1+|k|₁)^c e^{2π|k|₁(s-σ)}`;
* (iii) `kamFourierBanach_summation`: the summation lemma (absolute and uniform convergence,
  holomorphy, periodicity, coefficients, bound);
* (iv) `kamFourierBanach_coeff_sub`, `kamFourierBanach_coeff_sub_le`: linearity and the
  parameter-difference version.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Banach-valued coefficient decay** (blueprint `bpW:w1:fourier-banach` (i)). -/
theorem kamFourierBanach_coeff_le {s M : ℝ} (hs : 0 < s) {u : (Fin n → ℂ) → F}
    (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) (k : Fin n → ℤ) :
    ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ ≤
      M * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) := by
  have h := decay_boundary_radius hs hu hp hM k
  calc _ ≤ _ := h
    _ = _ := by rw [mul_comm]; congr 2; ring

/-- **Lattice sum** (blueprint `bpW:w1:fourier-banach` (ii), first part): for `0 < σ < s`,
`∑ₖ ‖û_k‖ e^{2π|k|₁(s-σ)} ≤ M coth(πσ)ⁿ`. -/
theorem kamFourierBanach_sum_le {s σ M : ℝ} (hσ : 0 < σ) (hσs : σ < s) {u : (Fin n → ℂ) → F}
    (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) :
    Summable (fun k => ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)) ∧
      ∑' k, ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
        (Real.cosh (Real.pi * σ) / Real.sinh (Real.pi * σ)) ^ n * M :=
  summableWeighted_torusCoeffW hσ hσs hu hp hM

/-- **Weighted lattice sum** (blueprint `bpW:w1:fourier-banach` (ii), second part): for `n ≥ 1`,
`0 < σ < s` and `c ≥ 0`,
`∑ₖ (1+|k|₁)^c ‖û_k‖ e^{2π|k|₁(s-σ)} ≤ M S_{n,c}(σ)`. -/
theorem kamFourierBanach_weighted_sum_le (hn : 1 ≤ n) {s σ M c : ℝ} (hc : 0 ≤ c) (hσ : 0 < σ)
    (hσs : σ < s) {u : (Fin n → ℂ) → F} (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    (hM : ∀ z ∈ complexStrip n s, ‖u z‖ ≤ M) :
    Summable (fun k => (1 + Fourier.modeSize k) ^ c *
        ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)) ∧
      ∑' k, (1 + Fourier.modeSize k) ^ c * ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤ M * kamLatticeConst n c σ := by
  have hs : 0 < s := hσ.trans hσs
  obtain ⟨hsum, hle⟩ := kamLattice_tsum_pow_exp_le hn hc hσ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 fun i => by simpa using hs)
  have hpt : ∀ k : Fin n → ℤ, (1 + Fourier.modeSize k) ^ c *
        ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
      M * ((1 + Fourier.modeSize k) ^ c * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
    intro k
    have hk := Fourier.modeSize_nonneg k
    have hd := kamFourierBanach_coeff_le hs hu hp hM k
    have hE : Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) =
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + Fourier.modeSize k) ^ c * ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)
        ≤ (1 + Fourier.modeSize k) ^ c * (M * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := by gcongr
      _ = M * ((1 + Fourier.modeSize k) ^ c *
          (Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
            Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k))) := by ring
      _ = _ := by rw [hE]
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ (1 + Fourier.modeSize k) ^ c *
        ‖torusCoeffW (fun x => u fun j => (x j : ℂ)) k‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) :=
    fun k => by have := Fourier.modeSize_nonneg k; positivity
  have hS := Summable.of_nonneg_of_le hnn hpt (hsum.mul_left M)
  refine ⟨hS, (Summable.tsum_le_tsum hpt hS (hsum.mul_left M)).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hle hM0

/-- **Summation** (blueprint `bpW:w1:fourier-banach` (iii)): if `∑ ‖c_k‖ e^{2π|k|₁ρ} < ∞` for some
`ρ > 0`, then `v(θ) = ∑ c_k e^{2πik·θ}` converges absolutely and uniformly on `T_ρ`, is
holomorphic and `1`-periodic there, has coefficients `c_k`, and `‖v(θ)‖ ≤ ∑ ‖c_k‖ e^{2π|k|₁ρ}`. -/
theorem kamFourierBanach_summation {ρ : ℝ} (hρ : 0 < ρ) {a : (Fin n → ℤ) → F}
    (ha : Summable fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) :
    (∀ θ ∈ complexStrip n ρ, Summable fun k => ‖character k θ • a k‖) ∧
    TendstoUniformlyOn (fun (N : ℕ) (θ : Fin n → ℂ) =>
        ∑ k ∈ modeCutoff n N, character k θ • a k) (fourierSumVec a) Filter.atTop
      (complexStrip n ρ) ∧
    (∀ θ ∈ complexStrip n ρ,
      ‖fourierSumVec a θ‖ ≤ ∑' k, ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) ∧
    DifferentiableOn ℂ (fourierSumVec a) (complexStrip n ρ) ∧
    (∀ (i : Fin n) z, z ∈ complexStrip n ρ →
      fourierSumVec a (z + Pi.single i 1) = fourierSumVec a z) ∧
    (∀ k, torusCoeffW (fun x => fourierSumVec a fun j => (x j : ℂ)) k = a k) :=
  summation_forward_vec hρ.le ha

omit [CompleteSpace F] in
/-- **Linearity** (blueprint `bpW:w1:fourier-banach` (iv)): the coefficient of a difference of two
continuous maps on the real torus is the difference of the coefficients. -/
theorem kamFourierBanach_coeff_sub {v w : (Fin n → ℝ) → F} (hv : Continuous v) (hw : Continuous w)
    (k : Fin n → ℤ) : torusCoeffW (fun x => v x - w x) k = torusCoeffW v k - torusCoeffW w k := by
  have hL : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hchar : Continuous fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character (-k)).continuous.comp hL
  unfold torusCoeffW torusAverage
  simp_rw [smul_sub]
  exact MeasureTheory.integral_sub (integrableOn_unitCube_of_continuous (hchar.smul hv))
    (integrableOn_unitCube_of_continuous (hchar.smul hw))

/-- **Parameter differences** (blueprint `bpW:w1:fourier-banach` (iv)): if `u₁, u₂` are holomorphic
and `1`-periodic on `T_s` and `‖u₁ - u₂‖ ≤ M` there, then the coefficients of `u₁` and `u₂`
differ by at most `M e^{-2π|k|₁s}` in norm. -/
theorem kamFourierBanach_coeff_sub_le {s M : ℝ} (hs : 0 < s) {u₁ u₂ : (Fin n → ℂ) → F}
    (h₁ : DifferentiableOn ℂ u₁ (complexStrip n s)) (h₂ : DifferentiableOn ℂ u₂ (complexStrip n s))
    (hp₁ : ∀ (i : Fin n) z, z ∈ complexStrip n s → u₁ (z + Pi.single i 1) = u₁ z)
    (hp₂ : ∀ (i : Fin n) z, z ∈ complexStrip n s → u₂ (z + Pi.single i 1) = u₂ z)
    (hM : ∀ z ∈ complexStrip n s, ‖u₁ z - u₂ z‖ ≤ M) (k : Fin n → ℤ) :
    ‖torusCoeffW (fun x => u₁ fun j => (x j : ℂ)) k -
        torusCoeffW (fun x => u₂ fun j => (x j : ℂ)) k‖ ≤
      M * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) := by
  have hc : ∀ u : (Fin n → ℂ) → F, DifferentiableOn ℂ u (complexStrip n s) →
      Continuous fun x : Fin n → ℝ => u fun j => (x j : ℂ) := fun u hu =>
    hu.continuousOn.comp_continuous
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
      fun x => ofReal_mem_complexStrip hs x
  rw [← kamFourierBanach_coeff_sub (hc _ h₁) (hc _ h₂)]
  exact kamFourierBanach_coeff_le hs (h₁.sub h₂)
    (fun i z hz => by simp only [Pi.sub_apply, hp₁ i z hz, hp₂ i z hz]) hM k

end KAM.Wave
