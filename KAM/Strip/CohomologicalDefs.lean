/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.FourierSeries
public import KAM.Diophantine.Cohomological

/-!
# Definitions of the cohomological interface (Part 1 to Parts 2 and 3)

This file holds only the two definitions through which Parts 2 and 3 use blueprint
`bp:p1:cohomological`; the theorems about them are in `KAM.Strip.CohomologicalNodes`.

* `KAM.cohConst n τ` is the constant `c(n, τ)` of `bp:p1:cohomological`, with the value fixed in its
  proof, `c(n, τ) = (2π)⁻¹ (τ / (eπ))^τ (8n / π)^n`.
* `KAM.cohSolution ω g` is the solution operator `𝓡`: the Fourier series with coefficients
  `ĝ_k / (2πi k·ω)` for `k ≠ 0` and `0` for `k = 0`. It is a total function, meaningful on strips
  where `g` is holomorphic, bounded, periodic and has zero average. It is definitionally the
  Fourier series `KAM.fourierSum` of the coefficients `Diophantine.solve ω (torusCoeff …)`
  (`KAM.cohSolution_eq_fourierSum`).
-/

@[expose] public noncomputable section

namespace KAM

/-- The constant `c(n, τ)` of `bp:p1:cohomological` (value fixed in its proof, p1 L897–900). -/
def cohConst (n : ℕ) (τ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * (τ / (Real.exp 1 * Real.pi)) ^ τ * (8 * (n : ℝ) / Real.pi) ^ n

/-- The solution operator `𝓡` of `bp:p1:cohomological`: the Fourier series with coefficients
`ĝ_k / (2πi k·ω)` (`k ≠ 0`) and `0` (`k = 0`). Total; meaningful on strips where `g` is
holomorphic, bounded, periodic, with zero average. -/
def cohSolution {n : ℕ} (ω : Fin n → ℝ) (g : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun θ => ∑' k : Fin n → ℤ,
    Diophantine.solve ω (torusCoeff (fun x => g (fun j => (x j : ℂ)))) k * character k θ

/-- `cohSolution` is, by definition, the Fourier series `KAM.fourierSum` of the coefficients
`Diophantine.solve ω (torusCoeff …)`. -/
theorem cohSolution_eq_fourierSum {n : ℕ} (ω : Fin n → ℝ) (g : (Fin n → ℂ) → ℂ) :
    cohSolution ω g =
      fourierSum (Diophantine.solve ω (torusCoeff (fun x => g (fun j => (x j : ℂ))))) := rfl

end KAM

end
