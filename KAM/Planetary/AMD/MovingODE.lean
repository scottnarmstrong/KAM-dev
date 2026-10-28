/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Basic
public import KAM.ODE.Hamiltonian
public import KAM.Planetary.Newtonian.Models
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn

/-!
# AMD confinement: the moving-frame system as an ODE on the collision-free domain

Blueprint `bpP:p14:moving-ode`: the collision-free domain is open, the Hamiltonian vector field of
the moving Hamiltonian is `C¹` on it, and the frozen solution predicate `IsMovingSolutionOn` is
literally `KAM.ODE.IsSolutionIn` for this field in the collision-free domain.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {n : ℕ}

theorem moving_ode (m : Fin n → ℝ) (mu : ℝ) :
    IsOpen (collisionFreeDomain n) ∧
    ContDiffOn ℝ 1 (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu))
      (collisionFreeDomain n) ∧
    ∀ (J : Set ℝ) (z : ℝ → Phase (n * 2)), IsMovingSolutionOn m mu J z ↔
      KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField (movingHamiltonian 1 1 m mu))
        (collisionFreeDomain n) J z := by
  have hW := isOpen_collisionFreeDomain n
  have hA := analyticOnNhd_movingHamiltonian 1 1 m mu (n := n)
  refine ⟨hW, KAM.ODE.ham_smooth_c1 hW (hA.contDiffOn hW.uniqueDiffOn), ?_⟩
  intro J z
  constructor
  · rintro ⟨h, hc⟩ t ht
    exact ⟨hc t ht, (h t ht).2.2⟩
  · intro h
    exact ⟨fun t ht => ⟨Set.mem_univ _,
      (analyticOnNhd_movingHamiltonian 1 1 m mu _ (h t ht).1).differentiableAt, (h t ht).2⟩,
      fun t ht => (h t ht).1⟩

end KAM.Planetary

end
