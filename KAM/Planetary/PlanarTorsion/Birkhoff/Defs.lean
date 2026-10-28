/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Frame
public import KAM.Planetary.PlanarTorsion.Beta
public import KAM.Planetary.PlanarTorsion.Homological
public import KAM.Planetary.PlanarTorsion.Lift.Defs
public import KAM.Planetary.Hamiltonian.Chart
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm

/-!
# Planar quartic torsion: the signed definitions of the Birkhoff theorem (package T16)

Blueprint P, Part 11b (`bpP:p11b:birkhoff-form`).  The nonresonance polynomial `p11c_phi4` and the
output predicate `PlanarBirkhoffResult` are exactly the signed declarations; they are split into this
leaf module so that the proof modules `Birkhoff/*` can use them, and re-exported by the facade
`PlanarTorsion/Birkhoff`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-- Simultaneous nonresonance polynomial; Part 9's Phi4 adapter, all modes 0<|k|1<=4. -/
def p11c_phi4 (p : PlanarData) (a : Fin 2 → ℝ) : ℝ :=
  ∏ k ∈ (Finset.univ : Finset (Fin 2 → Fin 9)).filter
    (fun k => 0 < (∑ i, |((k i).val : ℤ) - 4|) ∧ (∑ i, |((k i).val : ℤ) - 4|) ≤ 4),
    ∑ i, (((k i).val : ℝ) - 4) * p11c_sigma p a i

/-- Physical local normalisation, both physical perturbations, SAME coordinate map.
The output includes chart and domain, so neither is smuggled into a standing hypothesis. -/
def PlanarBirkhoffResult (p : PlanarData) (a0 : Fin 2 → ℝ) (rho : ℝ)
    (Oa : Set (Fin 2 → ℝ)) (r C : ℝ) : Prop :=
    ∃ O' : Set (Fin 2 → ℝ), IsOpen O' ∧ p.actions '' closedBall a0 rho ⊆ O' ∧
      IsCompact (closure O') ∧ closure O' ⊆ p.actions '' Oa ∧
      ∃ F chi : QuarticFamily O',
        (∀ I ∈ O', ∀ z, F.eval I z = p11c_quartic (p11c_coeffs p (p.axes I))
          (p11c_rotateSlow (p11c_frame p (p.axes I)) z)) ∧
        (∀ I ∈ O', chi.eval I = p11c_chi F (fun J j => 2 * p11c_sigma p (p.axes J) j) I) ∧
        ∃ T : Phase (2 + 2) → Phase (2 + 2),
        T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval ∧
        (∀ I ∈ O', ∀ j, 2 * p11c_sigma p (p.axes I) j < 0) ∧
        IsChart 1 T (p11c_tube O' r) ∧ InjOn T (p11c_tube O' r) ∧
        (∀ w ∈ p11c_tube O' r, (fun i => (T w).2 (Fin.castAdd 2 i)) =
          (fun i => w.2 (Fin.castAdd 2 i))) ∧
        (∀ w ∈ p11c_tube O' r, ∀ c : Fin 2 → ℝ,
          T (w + (Fin.append c 0, 0)) = T w + (Fin.append c 0, 0)) ∧
        (∀ w ∈ p11c_tube O' r, T w ∈ poincareProdDom 2 ∧
          NoCollision (poincareProd p.m p.kappa (T w)).1) ∧
        ∀ fhat ∈ ({p11c_hatFix p, p11c_hatMov p} : Set (Phase (2 + 2) → ℝ)),
          AnalyticOnNhd ℝ (fhat ∘ T) (p11c_tube O' r) ∧
          ∃ P0 : (Fin 2 → ℝ) → ℝ, (∀ I ∈ p.actions '' closedBall a0 rho,
            P0 I = p11c_secular fhat I 0) ∧
          (∀ I ∈ p.actions '' closedBall a0 rho, ∀ z : Phase 2, p11c_slowLength z < r →
            |p11c_secular (fhat ∘ T) I z - (P0 I +
              (∑ j, 2 * p11c_sigma p (p.axes I) j * oscillatorAction z.2 z.1 j) +
              (1 / 2 : ℝ) * ∑ i, ∑ j, p11c_beta p (p.axes I) i j *
                oscillatorAction z.2 z.1 i * oscillatorAction z.2 z.1 j)| ≤ C * (p11c_slowLength z) ^ 6) ∧
          ∀ mu0 : ℝ, 0 < mu0 → ∀ r0 : ℝ, 0 < r0 → r0 ≤ r / sqrt 2 →
            HasSecularBirkhoffForm (fun _ => fhat ∘ T)
              (interior (p.actions '' closedBall a0 rho)) r0 mu0 (fun _ => P0)
              (fun _ I j => 2 * p11c_sigma p (p.axes I) j) (fun _ I => p11c_beta p (p.axes I))

end KAM.Planetary

end
