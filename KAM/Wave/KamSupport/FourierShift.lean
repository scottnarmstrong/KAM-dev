/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.FourierSeriesVector
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fourier coefficients under an imaginary shift (blueprint-W `bpW:w1:fourier-shift`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

For `u : T_s → F` holomorphic and `1`-periodic with values in a complex Banach space `F`, and
`η ∈ ℝⁿ` with `|η_i| < s`:
`∫_{[0,1]ⁿ} u(x + iη) e^{-2πik·x} dx = e^{-2πk·η} û_k`.

Route: track K's `KAM.torusAverage_imag_shift` (the average of a bounded holomorphic periodic
scalar function is unchanged by an imaginary shift; its proof differentiates the average in the
shift size, instead of the coordinatewise rectangle argument of the blueprint), applied to `φ ∘ u`
for `φ ∈ F*`; boundedness on `T_ρ`, `max|η_i| < ρ < s`, is `KAM.periodic_bounded`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM MeasureTheory

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `χ_{-k}(iη) = e^{2π k·η}`. -/
theorem kamCharacter_neg_imag (k : Fin n → ℤ) (t : Fin n → ℝ) :
    character (-k) (fun j => (t j : ℂ) * Complex.I) =
      ((Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * t j) : ℝ) : ℂ) := by
  unfold character
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply, Int.cast_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Continuous linear functionals commute with the torus average of continuous maps. -/
theorem kamTorusAverage_clm {v : (Fin n → ℝ) → F} (hv : Continuous v) (φ : F →L[ℂ] ℂ) :
    φ (torusAverage v) = torusAverage fun x => φ (v x) := by
  have hint : Integrable v (volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    integrableOn_unitCube_of_continuous hv
  have := (φ.restrictScalars ℝ).integral_comp_comm hint
  unfold torusAverage
  simpa using this.symm

/-- **Fourier coefficients under an imaginary shift** (blueprint `bpW:w1:fourier-shift`):
for `u : T_s → F` holomorphic and `1`-periodic, `|η_i| < s`, `k ∈ ℤⁿ`,
`∫ u(x + iη) e^{-2πik·x} dx = e^{-2πk·η} û_k`. -/
theorem kamFourier_shift {s : ℝ} (hs : 0 < s) {u : (Fin n → ℂ) → F}
    (hu : DifferentiableOn ℂ u (complexStrip n s))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n s → u (z + Pi.single i 1) = u z)
    {η : Fin n → ℝ} (hη : ∀ i, |η i| < s) (k : Fin n → ℤ) :
    torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) •
        u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I)) =
      ((Real.exp (-(2 * Real.pi * ∑ j, (k j : ℝ) * η j)) : ℝ) : ℂ) •
        torusCoeffW (fun x => u fun j => (x j : ℂ)) k := by
  have hρ' : ‖η‖ < s := (pi_norm_lt_iff hs).2 fun i => by simpa using hη i
  have hρ'0 : 0 ≤ ‖η‖ := norm_nonneg _
  set ρ' := ‖η‖ with hρ'def
  set ρ := (ρ' + s) / 2 with hρdef
  have hρρ' : ρ' < ρ := by rw [hρdef]; linarith
  have hρs : ρ < s := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hsub : complexStrip n ρ ⊆ complexStrip n s := fun θ hθ i => (hθ i).trans hρs
  have hu' : DifferentiableOn ℂ u (complexStrip n ρ) := hu.mono hsub
  have hp' : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z :=
    fun i z hz => hp i z (hsub hz)
  obtain ⟨A, hA⟩ := periodic_bounded hu hp hρs
  have hLcont : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hshift_mem : ∀ x : Fin n → ℝ,
      ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I) ∈ complexStrip n s := by
    intro x j
    have him : (((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I) j).im = η j := by
      simp [Complex.mul_im]
    rw [him]; exact hη j
  have hucont : Continuous fun x : Fin n → ℝ =>
      u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I) :=
    hu.continuousOn.comp_continuous (hLcont.add continuous_const) hshift_mem
  have hu0cont : Continuous fun x : Fin n → ℝ => u fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous hLcont fun x => ofReal_mem_complexStrip hs x
  have hchar : Continuous fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character (-k)).continuous.comp hLcont
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun φ => ?_
  -- the scalar function
  set g : (Fin n → ℂ) → ℂ := fun θ => character (-k) θ * φ (u θ) with hg_def
  have hg : DifferentiableOn ℂ g (complexStrip n ρ) :=
    (differentiable_character (-k)).differentiableOn.mul
      (φ.differentiable.comp_differentiableOn hu')
  have hgp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z := by
    intro i z hz
    simp only [hg_def, character_add_single, hp' i z hz]
  have hgA : ∀ z ∈ complexStrip n ρ,
      ‖g z‖ ≤ Real.exp (2 * Real.pi * ρ * Fourier.modeSize (-k)) * (‖φ‖ * A) := by
    intro z hz
    rw [hg_def, norm_mul]
    refine mul_le_mul (norm_character_le (-k) hz) ?_ (norm_nonneg _) (Real.exp_pos _).le
    exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hA z hz) (norm_nonneg φ))
  have hs0 := torusAverage_imag_shift hρ'0 hρρ' hg hgp hgA
    (t := η) (fun j => by simpa [hρ'def] using norm_le_pi_norm η j)
  set c : ℝ := Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * η j) with hc
  have hcpos : 0 < c := Real.exp_pos _
  -- left side
  have hL : φ (torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) •
        u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I))) =
      torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) *
        φ (u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I))) := by
    rw [kamTorusAverage_clm (v := fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) •
      u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I)) (hchar.smul hucont) φ]
    simp only [map_smul, smul_eq_mul]
  have hR : φ (torusCoeffW (fun x => u fun j => (x j : ℂ)) k) =
      torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) *
        φ (u fun j => (x j : ℂ))) := clm_torusCoeffW hu0cont φ k
  have hexp : ∀ x : Fin n → ℝ, g ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I) =
      (c : ℂ) * (character (-k) (fun j => (x j : ℂ)) *
        φ (u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I))) := by
    intro x
    simp only [hg_def, character_add, kamCharacter_neg_imag, hc]
    ring
  have hlhs : torusAverage (fun x : Fin n → ℝ =>
      g ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I)) =
      (c : ℂ) * torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) *
        φ (u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I))) := by
    simp only [hexp]
    unfold torusAverage
    rw [integral_const_mul]
  rw [hlhs] at hs0
  have he : ((Real.exp (-(2 * Real.pi * ∑ j, (k j : ℝ) * η j)) : ℝ) : ℂ) * (c : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc, ← Real.exp_add]; simp
  rw [hL, map_smul, smul_eq_mul, hR]
  have hs0' : (c : ℂ) * torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) *
        φ (u ((fun j => (x j : ℂ)) + fun j => (η j : ℂ) * Complex.I))) =
      torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) *
        φ (u fun j => (x j : ℂ))) := hs0
  rw [← hs0', ← mul_assoc, he, one_mul]

end KAM.Wave
