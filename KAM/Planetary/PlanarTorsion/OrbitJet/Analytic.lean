/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Planetary.Poincare.Chart
public import KAM.Kepler.Equation

/-!
# Planar quartic torsion: the unit-axis orbit, analyticity and the Poincaré bridge

Blueprint P, Part 11b (`bpP:p11b:orbit`): the unit-axis physical position `p11c_orbit` built from
the regular Kepler solution `keplerLong`, the displayed degree-four Laurent jet `p11c_orbitJet`,
the jet-equality predicate `p11c_JetEq`, analyticity of the orbit on the open eccentricity disc
(`orbit_analytic`) and its identification with the delivered Poincaré chart
(`orbit_poincare_bridge`).  The jet identification itself is in `OrbitJet/Expansion`.
-/

@[expose] public noncomputable section

open Set Metric Real Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler

/-- Unit-axis physical position, from the existing regular Kepler solution. -/
def p11c_orbit (lam : ℝ) (v : Fin 2 → ℝ) : ℂ :=
  let F := keplerLong lam v
  let k := sqrt (1 - planeSq v)
  let q := k • orbitalUnit F - v + (planeDot v (orbitalUnit F) / (1 + k)) • v
  (q 0 : ℂ) + Complex.I * (q 1 : ℂ)

def p11c_orbitJet (lam : ℝ) (v : Fin 2 → ℝ) : ℂ :=
  let X := Complex.exp (Complex.I * lam)
  let z : ℂ := (v 0 : ℂ) + Complex.I * (v 1 : ℂ)
  let b := star z
  X + (X ^ 2 * b / 2 - 3 * z / 2) +
    (3 * X ^ 3 * b ^ 2 / 8 - X * z * b / 2 + X⁻¹ * z ^ 2 / 8) +
    (X ^ 4 * b ^ 3 / 3 - 3 * X ^ 2 * z * b ^ 2 / 8 + X ^ (-2 : ℤ) * z ^ 3 / 24) +
    (125 * X ^ 5 * b ^ 4 / 384 - 3 * X ^ 3 * z * b ^ 3 / 8 - X * z ^ 2 * b ^ 2 / 64 +
      X⁻¹ * z ^ 3 * b / 24 + 3 * X ^ (-3 : ℤ) * z ^ 4 / 128)

def p11c_JetEq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (f g : E → F) : Prop :=
  ∀ j ≤ k, iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j g 0

section Aux

private theorem planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem planeSq_lt_one {v : Fin 2 → ℝ} (hv : planeLength v < 1) : planeSq v < 1 := by
  have h : planeLength v ^ 2 < 1 := by
    have := planeLength_nonneg v; nlinarith
  rwa [planeLength_sq] at h

private theorem analyticAt_apply (i : Fin 2) (v : Fin 2 → ℝ) :
    AnalyticAt ℝ (fun v : Fin 2 → ℝ => v i) v :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).analyticAt v

/-- The real components of the unit-axis position are analytic on `ℓ v < 1`. -/
private theorem analyticAt_orbit_component (lam : ℝ) {v : Fin 2 → ℝ} (hv : planeLength v < 1)
    (i : Fin 2) :
    AnalyticAt ℝ (fun v : Fin 2 → ℝ =>
      (sqrt (1 - planeSq v) • orbitalUnit (keplerLong lam v) - v +
        (planeDot v (orbitalUnit (keplerLong lam v)) / (1 + sqrt (1 - planeSq v))) • v) i) v := by
  have hF : AnalyticAt ℝ (fun v : Fin 2 → ℝ => keplerLong lam v) v :=
    AnalyticAt.comp (g := fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) (f := fun v => (lam, v))
      (analyticOnNhd_keplerLong (lam, v) hv) (analyticAt_const.prod analyticAt_id)
  have hcos : AnalyticAt ℝ (fun v : Fin 2 → ℝ => Real.cos (keplerLong lam v)) v :=
    AnalyticAt.comp (g := Real.cos) (f := fun v : Fin 2 → ℝ => keplerLong lam v) (x := v)
      (Real.contDiff_cos (n := ω)).contDiffAt.analyticAt hF
  have hsin : AnalyticAt ℝ (fun v : Fin 2 → ℝ => Real.sin (keplerLong lam v)) v :=
    AnalyticAt.comp (g := Real.sin) (f := fun v : Fin 2 → ℝ => keplerLong lam v) (x := v)
      (Real.contDiff_sin (n := ω)).contDiffAt.analyticAt hF
  have hsq : AnalyticAt ℝ (fun v : Fin 2 → ℝ => planeSq v) v := by
    simp only [planeSq_two]
    exact ((analyticAt_apply 0 v).pow 2).add ((analyticAt_apply 1 v).pow 2)
  have hpos : 0 < 1 - planeSq v := sub_pos.2 (planeSq_lt_one hv)
  have hk : AnalyticAt ℝ (fun v : Fin 2 → ℝ => sqrt (1 - planeSq v)) v :=
    (((analyticAt_const.sub hsq).contDiffAt (n := ω)).sqrt hpos.ne').analyticAt
  have hk0 : 0 ≤ sqrt (1 - planeSq v) := Real.sqrt_nonneg _
  have hd : AnalyticAt ℝ
      (fun v : Fin 2 → ℝ => planeDot v (orbitalUnit (keplerLong lam v))) v := by
    simp only [planeDot_two, orbitalUnit, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ((analyticAt_apply 0 v).mul hcos).add ((analyticAt_apply 1 v).mul hsin)
  have hm : AnalyticAt ℝ (fun v : Fin 2 → ℝ =>
      planeDot v (orbitalUnit (keplerLong lam v)) / (1 + sqrt (1 - planeSq v))) v :=
    hd.div (analyticAt_const.add hk) (by linarith)
  fin_cases i
  · simp only [Fin.zero_eta, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbitalUnit,
      Matrix.cons_val_zero]
    exact ((hk.mul hcos).sub (analyticAt_apply 0 v)).add (hm.mul (analyticAt_apply 0 v))
  · simp only [Fin.mk_one, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbitalUnit,
      Matrix.cons_val_one]
    exact ((hk.mul hsin).sub (analyticAt_apply 1 v)).add (hm.mul (analyticAt_apply 1 v))

end Aux

theorem orbit_analytic (lam : ℝ) :
    AnalyticOnNhd ℝ (p11c_orbit lam) {v | planeLength v < 1} := by
  intro v hv
  have h0 := analyticAt_orbit_component lam hv 0
  have h1 := analyticAt_orbit_component lam hv 1
  have e : p11c_orbit lam = fun v : Fin 2 → ℝ =>
      Complex.ofRealCLM
          ((sqrt (1 - planeSq v) • orbitalUnit (keplerLong lam v) - v +
            (planeDot v (orbitalUnit (keplerLong lam v)) / (1 + sqrt (1 - planeSq v))) • v) 0) +
        Complex.I * Complex.ofRealCLM
          ((sqrt (1 - planeSq v) • orbitalUnit (keplerLong lam v) - v +
            (planeDot v (orbitalUnit (keplerLong lam v)) / (1 + sqrt (1 - planeSq v))) • v) 1) := by
    funext v; simp [p11c_orbit]
  rw [e]
  exact (Complex.ofRealCLM.analyticAt _ |>.comp h0).add
    (analyticAt_const.mul (Complex.ofRealCLM.analyticAt _ |>.comp h1))

theorem orbit_poincare_bridge (lam L : ℝ) (hL : 0 < L) (u : Fin 2 → ℝ)
    (hu : planeSq u / 2 < L) :
    let w : Phase 2 := (![lam, u 0], ![L, u 1])
    let q := (poincare 1 (L ^ 2) w).1
    (q 0 : ℂ) + Complex.I * (q 1 : ℂ) = p11c_orbit lam (poincareV w) := by
  intro w q
  have hw : w ∈ poincareDom := by
    refine ⟨hL, ?_⟩
    simp only [poincareGamma, w, planeSq_two] at hu ⊢
    simpa using hu
  obtain ⟨-, hK, -, -, hsq, -, -⟩ := poincare_facts hw
  have hk : sqrt (1 - planeSq (poincareV w)) = poincareK w := by
    rw [hsq]; simp [Real.sqrt_sq hK.le]
  have hpref : w.2 0 ^ 2 / (1 ^ 2 * L ^ 2) = 1 := by
    have : w.2 0 = L := rfl
    rw [this]; field_simp
  have hF : poincareF w = keplerLong lam (poincareV w) := rfl
  simp only [q, p11c_orbit, poincare, hk, hpref, one_smul, hF]

end KAM.Planetary

end
