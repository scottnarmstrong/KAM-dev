/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.GoodAxes.Block
public import KAM.Planetary.SecularSpectrum.TwoPlanets

/-!
# Good axes: the sorted eigenvalues are analytic on the simple locus

Blueprint P, Part 10 (`bpP:p10:sorted-analytic`, `stepP:p10:sa-loc`): at a point of `simpleAxes D`
the analytic branches of `local_analytic` are all the eigenvalues, hence agree with `sigma D`.  The
second sentence of the blueprint (`stepP:p10:sa-n2`, `U₂ = A₂`) is `SecularSpectrum.n2` together with
`SecularSpectrum.sigma_two_lt`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- The sorted spectrum of an orthogonally diagonalised matrix with strictly increasing spectrum. -/
lemma sorted_eq_of_frame {M R : Mat n} {s : Vec n} (hM : M.IsHermitian) (hR : R.transpose * R = 1)
    (hs : StrictMono s) (h : M = R * Matrix.diagonal s * R.transpose) : sorted M hM = s := by
  have hcp : M.charpoly = ∏ i, (X - C (s i) : ℝ[X]) := by
    rw [h, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hR, Matrix.mul_one,
      Matrix.charpoly_diagonal]
  refine eq_of_monotone_prod (sorted_monotone hM) hs.monotone ?_
  rw [← charpoly_eq_prod_sorted hM, hcp]

theorem sorted_analytic (D : Data n) : AnalyticOnNhd ℝ (sigma D) (simpleAxes D) := by
  intro a ha
  have hinj : Function.Injective (sigma D a) := (discriminant_ne_zero_iff _).1 ha.2
  obtain ⟨r, hr, hball, s, R, hs, -, hfr⟩ := local_analytic (isOpen_axes n)
    (fun x _ => coeffs_hermitian D x) (coeffs_analytic D) ha.1
    (eigenvalues_injective_of_sorted _ hinj)
  refine (hs a (Metric.mem_ball_self hr)).congr ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with x hx
  obtain ⟨hSO, hmono, hM⟩ := hfr x hx
  exact (sorted_eq_of_frame (coeffs_hermitian D x) hSO.1 hmono hM).symm

end Nondegeneracy
end KAM.Planetary
end
