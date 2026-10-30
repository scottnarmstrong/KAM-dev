/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Cohomological
public import KAM.Strip.CohomologicalParsevalBessel
public import KAM.Strip.CohomologicalParsevalLattice
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Parseval bound for the cohomological solution

For `ω` `(γ, τ)`-Diophantine and `g` holomorphic, `1`-periodic, bounded by `A` on `T_ρ` with zero
average, `‖𝓡 g‖ ≤ cohConstP n τ / (γ δ^{τ+n/2}) A` on `T_{ρ-δ}`
(`KAM.norm_cohSolution_parseval_le`), for every `0 < δ < ρ` (no restriction `δ ≤ 1`).

With `ρ' = ρ - δ/2`, Cauchy–Schwarz splits `∑ |û_k| e^{2π(ρ-δ)|k|₁}` into
`(∑ |ĝ_k|² e^{4πρ'|k|₁})^{1/2}` (at most `(2ⁿ A²)^{1/2}` by `KAM.sum_sq_torusCoeff_exp_le`) and
`(2πγ)⁻¹ (∑_{k≠0} |k|₁^{2τ} e^{-2πδ|k|₁})^{1/2}` (`KAM.sum_modeSize_rpow_exp_le`).
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- **The Parseval cohomological estimate** (scalar): `‖𝓡 g‖ ≤ cohConstP n τ / (γ δ^{τ+n/2}) A`. -/
theorem norm_cohSolution_parseval_le {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ}
    (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
    (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolution ω g θ‖ ≤ cohConstP n τ / (γ * δ ^ (τ + (n : ℝ) / 2)) * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hρ 0))
  obtain ⟨hsum, -⟩ := summableWeighted_solve_torusCoeff hω hγ hτ hδ hδρ hg hp hA h0
  set a : (Fin n → ℤ) → ℂ := torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ) with ha_def
  set D : ℝ := δ ^ (τ + (n : ℝ) / 2) with hD_def
  have hD : 0 < D := Real.rpow_pos_of_pos hδ _
  set Q : ℝ := (2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) * (8 * (n : ℝ) / Real.pi) ^ n with hQ_def
  have hQ0 : 0 ≤ Q := by positivity
  set ρ' : ℝ := ρ - δ / 2 with hρ'_def
  have hC : 0 ≤ 1 / (2 * Real.pi * γ) := by positivity
  -- the finite-sum bound
  have key : ∀ s : Finset (Fin n → ℤ),
      ∑ k ∈ s, ‖Diophantine.solve ω a k‖ * Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) ≤
        1 / (2 * Real.pi * γ) * (|A| / D * Real.sqrt (2 ^ n * Q)) := by
    intro s
    set x : (Fin n → ℤ) → ℝ := fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ' * Fourier.modeSize k)
      with hx_def
    set y : (Fin n → ℤ) → ℝ := fun k => Fourier.modeSize k ^ τ *
      Real.exp (-(Real.pi * δ) * Fourier.modeSize k) with hy_def
    have hterm : ∀ k ∈ s, ‖Diophantine.solve ω a k‖ *
        Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) ≤
        if k ≠ 0 then 1 / (2 * Real.pi * γ) * (x k * y k) else 0 := by
      intro k _
      by_cases hk : k = 0
      · subst hk
        simp
      · simp only [ne_eq, hk, not_false_eq_true, ite_true]
        have hn := Diophantine.norm_solve_le hω.condition hγ a hk
        calc _ ≤ (1 / (2 * Real.pi * γ) * (‖a k‖ * Fourier.modeSize k ^ τ)) *
              Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) :=
            mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
          _ = 1 / (2 * Real.pi * γ) * (x k * y k) := by
            simp only [hx_def, hy_def]
            have : Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) =
                Real.exp (2 * Real.pi * ρ' * Fourier.modeSize k) *
                  Real.exp (-(Real.pi * δ) * Fourier.modeSize k) := by
              rw [← Real.exp_add]
              congr 1
              rw [hρ'_def]
              ring
            rw [this]
            ring
    set s' := s.filter (· ≠ 0) with hs'
    have hsum_if : ∑ k ∈ s, (if k ≠ 0 then 1 / (2 * Real.pi * γ) * (x k * y k) else 0) =
        ∑ k ∈ s', 1 / (2 * Real.pi * γ) * (x k * y k) := by
      rw [hs', Finset.sum_filter]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [hsum_if, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hx2 : ∑ k ∈ s', x k ^ 2 ≤ 2 ^ n * A ^ 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun k _ _ => by positivity) ?_
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
        (sum_sq_torusCoeff_exp_le (ρ' := ρ') (by rw [hρ'_def]; linarith)
          (by rw [hρ'_def]; linarith) hg hp hA s)
      simp only [hx_def, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hy2 : ∑ k ∈ s', y k ^ 2 ≤ Q / D ^ 2 := by
      rw [hD_def, hQ_def, ← lattice_bound_eq hτ hδ]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
        (sum_modeSize_rpow_exp_le hτ hδ s)
      simp only [hy_def, mul_pow]
      rw [← Real.exp_nat_mul, ← Real.rpow_natCast, ← Real.rpow_mul (Fourier.modeSize_nonneg k)]
      congr 2
      · push_cast; ring_nf
      · push_cast; ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s' x y
    have hprod : (∑ k ∈ s', x k * y k) ^ 2 ≤ 2 ^ n * A ^ 2 * (Q / D ^ 2) :=
      hcs.trans (mul_le_mul hx2 hy2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity))
    have habs := Real.abs_le_sqrt hprod
    refine (le_abs_self _).trans (habs.trans (le_of_eq ?_))
    have : 2 ^ n * A ^ 2 * (Q / D ^ 2) = (A / D) ^ 2 * (2 ^ n * Q) := by
      field_simp
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hD]
  have hsum' : Summable fun k => ‖Diophantine.solve ω a k‖ *
      Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) := hsum
  have hw : Fourier.weightedNorm (2 * Real.pi * (ρ - δ)) (Diophantine.solve ω a) ≤
      1 / (2 * Real.pi * γ) * (|A| / D * Real.sqrt (2 ^ n * Q)) :=
    hsum'.tsum_le_of_sum_le key
  refine (norm_fourierSum_le hsum hθ).trans (hw.trans (le_of_eq ?_))
  rw [abs_of_nonneg hA0, cohConstP, ← hQ_def]
  have hγ' : γ ≠ 0 := hγ.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end KAM

end
