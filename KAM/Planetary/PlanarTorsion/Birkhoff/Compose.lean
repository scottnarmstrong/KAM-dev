/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Map

/-!
# Planar quartic torsion: composition of the lift and the rotation lift (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-rot#lift`).  `T = p11c_rotationLift p ∘ p11c_liftFlow chi` is
a chart, injective, action preserving and angle-translation covariant on every set `S` over which
`p11c_liftFlow chi` has these properties and whose actions lie in the frame domain
(`p11c_rotationLift_chart`).
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler

theorem p11cB_liftFlow_act (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (w : Phase (2 + 2)) :
    p11cL_act (p11c_liftFlow chi w) = p11cL_act w := by
  rw [p11cL_liftFlow_eq, p11cL_act_assemble]

theorem p11cB_T_props (p : PlanarData) (hp : p.Valid) (chi : (Fin 2 → ℝ) → Phase 2 → ℝ)
    {S : Set (Phase (2 + 2))} (hS : ∀ w ∈ S, p11cL_act w ∈ p11c_frameActionDomain p)
    (hch : IsChart 1 (p11c_liftFlow chi) S) (hinj : InjOn (p11c_liftFlow chi) S)
    (htr : ∀ w ∈ S, ∀ c : Fin 2 → ℝ,
      p11c_liftFlow chi (w + (Fin.append c 0, 0)) = p11c_liftFlow chi w + (Fin.append c 0, 0)) :
    IsChart 1 (p11c_rotationLift p ∘ p11c_liftFlow chi) S ∧
      InjOn (p11c_rotationLift p ∘ p11c_liftFlow chi) S ∧
      (∀ w ∈ S, (fun i => ((p11c_rotationLift p ∘ p11c_liftFlow chi) w).2 (Fin.castAdd 2 i)) =
        fun i => w.2 (Fin.castAdd 2 i)) ∧
      (∀ w ∈ S, ∀ c : Fin 2 → ℝ, (p11c_rotationLift p ∘ p11c_liftFlow chi) (w + (Fin.append c 0, 0))
        = (p11c_rotationLift p ∘ p11c_liftFlow chi) w + (Fin.append c 0, 0)) := by
  obtain ⟨hR1, hR2, hR3, hR4⟩ := p11c_rotationLift_chart p hp
  have hmaps : MapsTo (p11c_liftFlow chi) S
      (SecularSpectrum.liftDomain (p11c_frameActionDomain p)) := by
    intro w hw
    show fast (p11c_liftFlow chi w).2 ∈ p11c_frameActionDomain p
    have := p11cB_liftFlow_act chi w
    have h2 : fast (p11c_liftFlow chi w).2 = p11cL_act (p11c_liftFlow chi w) := rfl
    rw [h2, this]
    exact hS w hw
  refine ⟨?_, hR2.comp hinj hmaps, fun w hw => ?_, fun w hw c => ?_⟩
  · have := hch.comp hR1 hmaps
    simpa using this
  · have h1 := hR3 _ (hmaps hw)
    have h2 := p11cB_liftFlow_act chi w
    simp only [Function.comp]
    rw [h1]
    exact congrArg (fun f : Fin 2 → ℝ => f) h2
  · simp only [Function.comp]
    rw [htr w hw c]
    exact hR4 _ (hmaps hw) c

end KAM.Planetary

end
