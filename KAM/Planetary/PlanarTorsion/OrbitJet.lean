/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.OrbitJet.Polar
public import KAM.Planetary.PlanarTorsion.OrbitJet.Line

/-!
# Planar quartic torsion: the unit-axis orbit and its degree-four jet

Blueprint P, Part 11b (`bpP:p11b:orbit`).  The definitions `p11c_orbit`, `p11c_orbitJet`,
`p11c_JetEq`, `orbit_analytic` and `orbit_poincare_bridge` are in `OrbitJet/Analytic`; the jet
identification `orbit` is proved here from the line expansion of `OrbitJet/Line` and the
polarization argument of `OrbitJet/Polar` (`OrbitJet/Jet` and `OrbitJet/Algebra` hold the
elementary jet algebra and its exact polynomial identities).
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology Real
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler OrbitJet

private theorem p11c_orbitJet_line (lam : ℝ) (w : Fin 2 → ℝ) (t : ℝ) :
    p11c_orbitJet lam (t • w) =
      (refJet ((w 0 : ℂ) + Complex.I * (w 1 : ℂ)) ((w 0 : ℂ) - Complex.I * (w 1 : ℂ))
        (Complex.exp (Complex.I * lam)) (Complex.exp (-(Complex.I * lam)))).ev t := by
  have hX : (Complex.exp (Complex.I * lam))⁻¹ = Complex.exp (-(Complex.I * lam)) :=
    (Complex.exp_neg _).symm
  have h2 : (Complex.exp (Complex.I * lam)) ^ (-2 : ℤ) = Complex.exp (-(Complex.I * lam)) ^ 2 := by
    rw [zpow_neg, ← hX, inv_pow]; rfl
  have h3 : (Complex.exp (Complex.I * lam)) ^ (-3 : ℤ) = Complex.exp (-(Complex.I * lam)) ^ 3 := by
    rw [zpow_neg, ← hX, inv_pow]; rfl
  simp only [p11c_orbitJet, Jet5.ev, refJet, hX, h2, h3, Complex.star_def, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring_nf

private theorem analyticAt_p11c_orbitJet (lam : ℝ) : AnalyticAt ℝ (p11c_orbitJet lam) 0 := by
  have h0 : AnalyticAt ℝ (fun v : Fin 2 → ℝ => (v 0 : ℂ)) 0 :=
    (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).analyticAt 0)
  have h1 : AnalyticAt ℝ (fun v : Fin 2 → ℝ => (v 1 : ℂ)) 0 :=
    (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).analyticAt 0)
  have hz : AnalyticAt ℝ (fun v : Fin 2 → ℝ => (v 0 : ℂ) + Complex.I * (v 1 : ℂ)) 0 :=
    h0.add (analyticAt_const.mul h1)
  have hb : AnalyticAt ℝ (fun v : Fin 2 → ℝ => star ((v 0 : ℂ) + Complex.I * (v 1 : ℂ))) 0 := by
    have : (fun v : Fin 2 → ℝ => star ((v 0 : ℂ) + Complex.I * (v 1 : ℂ))) =
        fun v : Fin 2 → ℝ => (v 0 : ℂ) - Complex.I * (v 1 : ℂ) := by
      funext v; simp [sub_eq_add_neg]
    rw [this]
    exact h0.sub (analyticAt_const.mul h1)
  unfold p11c_orbitJet
  simp only
  fun_prop

/-- `bpP:p11b:orbit`: the unit-axis orbit is analytic at `v = 0` and its degree-four jet is the
displayed Laurent jet. -/
theorem orbit (lam : ℝ) :
    AnalyticAt ℝ (p11c_orbit lam) 0 ∧ p11c_JetEq 4 (p11c_orbit lam) (p11c_orbitJet lam) := by
  have h0 : AnalyticAt ℝ (p11c_orbit lam) 0 :=
    orbit_analytic lam 0 (by simp [planeLength, planeSq])
  refine ⟨h0, jetEq_of_line_isBigO h0 (analyticAt_p11c_orbitJet lam) fun w => ?_⟩
  have := (orbit_line_isJet lam w).bigO
  refine this.congr_left fun t => ?_
  rw [p11c_orbitJet_line]

end KAM.Planetary

end
