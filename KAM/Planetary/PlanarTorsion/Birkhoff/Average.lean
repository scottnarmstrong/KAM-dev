/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Map
public import KAM.Planetary.PlanarTorsion.Birkhoff.Jets

/-!
# Planar quartic torsion: the torus average of the transformed perturbation (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-avg`).  Since `T` only translates the angles over a point
`assemble I φ z.2 z.1` (`p11cB_T_assemble`) and the physical perturbations are `2π`-periodic in the
angles, the torus average of `f̂ ∘ T` at `(I, z)` is the torus average of `f̂` at the rotated flow
image (`p11cB_secular_T`).  The moving average differs from the fixed one by the action-only
constant `modelDelta` (`p11cB_secular_mov`).
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

/-- The torus average of a perturbation composed with an angle-translating map. -/
theorem p11cB_secular_T (p : PlanarData) (hp : p.Valid) (b : Bool) (P : Phase (2 + 2) → ℝ)
    (hP : ∀ w, P w = SecularForm.perturbation (p11cSecularData p hp) b w)
    (T : Phase (2 + 2) → Phase (2 + 2)) (I : Fin 2 → ℝ) (z Zs : Phase 2) (c : Fin 2 → ℝ)
    (hT : ∀ φ, T (assemble I φ z.2 z.1) = assemble I (φ + c) Zs.2 Zs.1)
    (hgood : assemble I c Zs.2 Zs.1 ∈ poincareProdDom 2) :
    p11c_secular (P ∘ T) I z =
      SecularForm.secular (p11cSecularData p hp) b (Zs.1, I, Zs.2) := by
  set D := p11cSecularData p hp with hD
  have hx : ((Zs.1, I, Zs.2) : SecularForm.Slow 2) ∈ SecularForm.slowDom D := by
    rw [SecularForm.mem_slowDom_iff]
    exact (SecularForm.assemble_mem_iff I c Zs.2 Zs.1).1 hgood
  have h1 : p11c_secular (P ∘ T) I z = (2 * π) ^ (-((2 : ℕ) : ℤ)) *
      ∫ φ in SecularForm.cell 2, (P ∘ T) (assemble I φ z.2 z.1) := rfl
  have h2 : SecularForm.secular D b (Zs.1, I, Zs.2) = (2 * π) ^ (-((2 : ℕ) : ℤ)) *
      ∫ φ in SecularForm.cell 2, SecularForm.perturbation D b (assemble I φ Zs.2 Zs.1) := rfl
  have hfun : (fun φ : Fin 2 → ℝ => (P ∘ T) (assemble I φ z.2 z.1)) =
      fun φ => SecularForm.perturbation D b (assemble I (φ + c) Zs.2 Zs.1) := by
    funext φ
    simp only [Function.comp]
    rw [hT, hP]
  have hcell := cell_integral_add (g := fun φ => SecularForm.perturbation D b
    (assemble I φ Zs.2 Zs.1)) (fun k t => SecularForm.perturbation_periodic D b hx k t) c
  rw [h1, h2, hfun]
  exact congrArg _ hcell

/-- The moving average is the fixed average plus the action-only constant. -/
theorem p11cB_secular_mov (p : PlanarData) (hp : p.Valid) (I : Fin 2 → ℝ) (y : Phase 2)
    (hgood : ∀ t, assemble I t y.2 y.1 ∈ p11cB_good p) :
    SecularForm.secular (p11cSecularData p hp) true (y.1, I, y.2) =
      SecularForm.secular (p11cSecularData p hp) false (y.1, I, y.2) +
        SecularForm.modelDelta (p11cSecularData p hp) I := by
  set D := p11cSecularData p hp with hD
  have hx : ((y.1, I, y.2) : SecularForm.Slow 2) ∈ SecularForm.slowDom D := by
    rw [SecularForm.mem_slowDom_iff]
    exact (SecularForm.assemble_mem_iff I 0 y.2 y.1).1 (hgood 0).1
  have hcont : Continuous (fun t : Fin 2 → ℝ =>
      SecularForm.perturbation D false (assemble I t y.2 y.1)) := by
    have h1 : ContinuousOn (fun w => SecularForm.perturbation D false w) (p11cB_good p) :=
      (analyticOnNhd_fFix_poincareProd hp.2.2 (mul_pos hp.1 hp.2.1)).continuousOn
    have h2 : Continuous (fun t : Fin 2 → ℝ => (assemble I t y.2 y.1 : Phase (2 + 2))) := by
      refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
          simp [Fin.append_left] <;> fun_prop
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
          simp [Fin.append_left] <;> fun_prop
    exact h1.comp_continuous h2 hgood
  exact (SecularForm.identification D hx).2.2.2
    (hcont.continuousOn.integrableOn_compact SecularForm.isCompact_cell)

end KAM.Planetary

end
