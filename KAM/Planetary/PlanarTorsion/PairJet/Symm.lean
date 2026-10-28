/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.PairJet.Terms

/-!
# Planar quartic torsion: periodicity and the antipodal symmetry of the pair average

Blueprint P, Part 11b (`stepP:p11b:pj-red`, symmetry (S1) of `bpP:p8:symmetries`): the unit-axis
orbit is `2π`-periodic in the mean longitude and satisfies
`z_orb(λ + π; -v) = - z_orb(λ; v)`.  Hence the pair average `p11c_pairAverage` is even in the
eccentricity vectors, so all its odd-order derivatives at `0` vanish.
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter KAM KAM.Kepler
open scoped Topology
namespace KAM.Planetary

private theorem p11cPJ_planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem p11cPJ_planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

theorem p11c_orbit_period {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    p11c_orbit (lam + 2 * π) v = p11c_orbit lam v := by
  have hF := keplerLong_shift hv lam
  have hc : Real.cos (keplerLong lam v + 2 * π) = Real.cos (keplerLong lam v) :=
    Real.cos_add_two_pi _
  have hs : Real.sin (keplerLong lam v + 2 * π) = Real.sin (keplerLong lam v) :=
    Real.sin_add_two_pi _
  simp only [p11c_orbit, hF, orbitalUnit, hc, hs]

theorem p11c_orbit_antipode {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    p11c_orbit (lam + π) (-v) = -p11c_orbit lam v := by
  have hv' : planeLength (-v) < 1 := by rwa [planeLength_neg]
  have hF : keplerLong (lam + π) (-v) = keplerLong lam v + π := by
    refine keplerLong_unique hv' ?_
    have h := keplerPhi_keplerLong hv lam
    simp only [keplerPhi] at h ⊢
    simp only [Pi.neg_apply, Real.sin_add_pi, Real.cos_add_pi]
    linarith
  have hsq : planeSq (-v) = planeSq v := by
    simp [p11cPJ_planeSq_two]
  simp only [p11c_orbit, hF, hsq, orbitalUnit, Real.cos_add_pi, Real.sin_add_pi,
    p11cPJ_planeDot_two, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring_nf

end KAM.Planetary

end
