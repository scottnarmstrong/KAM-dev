/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.QuarticFlow.Energy
public import KAM.Planetary.PlanarTorsion.QuarticFlow.Field

/-!
# Planar quartic torsion: the restricted flow and its specification (package T9)

Blueprint P, Part 11b (`bpP:p11b:flow`).  `p11c_flow` (copied verbatim from the signature file)
picks a solution on `[-1, 1]` when one exists.  By ODE uniqueness the choice is irrelevant:
`p11cQ_flow_eq` identifies the flow with every solution on `[-1, 1]`, and `p11cQ_flow_spec`
records existence, the initial value and the energy bound under the smallness condition
`32 C |z|² ≤ 1` for a cubic field bound `C`.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace KAM.Planetary

open KAM KAM.ODE

open Classical in
/-- Restricted time-one maps chosen by existence only; consumers use flow's specification. -/
def p11c_flow (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (I : Fin 2 → ℝ) (t : ℝ) (z : Phase 2) : Phase 2 :=
  if h : ∃ g : ℝ → Phase 2,
      IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1) g ∧ g 0 = z
  then h.choose t else z

/-- The Hamiltonian field of `-H` is the negative of the field of `H`. -/
theorem p11cQ_ham_neg {d : ℕ} (H : Phase d → ℝ) :
    hamiltonianVectorField (fun w => -H w) = fun z => -hamiltonianVectorField H z := by
  funext z
  unfold hamiltonianVectorField
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp

/-- The restricted flow agrees with every solution on `[-1, 1]` through the same point. -/
theorem p11cQ_flow_eq {chi : (Fin 2 → ℝ) → Phase 2 → ℝ} {I : Fin 2 → ℝ}
    (hF1 : ContDiffOn ℝ 1 (hamiltonianVectorField (chi I)) univ) {z : Phase 2} {g : ℝ → Phase 2}
    (hg : IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1) g) (hg0 : g 0 = z) :
    ∀ t ∈ Icc (-1 : ℝ) 1, p11c_flow chi I t z = g t := by
  intro t ht
  have h : ∃ g : ℝ → Phase 2,
      IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1) g ∧ g 0 = z := ⟨g, hg, hg0⟩
  unfold p11c_flow
  simp only [h, ↓reduceDIte]
  exact gen_uniqueness isOpen_univ hF1 ordConnected_Icc (t₀ := 0) ⟨by norm_num, by norm_num⟩
    h.choose_spec.1 hg (by rw [h.choose_spec.2, hg0]) ht

/-- Specification of the restricted flow for small initial slow length. -/
theorem p11cQ_flow_spec {chi : (Fin 2 → ℝ) → Phase 2 → ℝ} {I : Fin 2 → ℝ} {C : ℝ} (hC : 0 < C)
    (hF1 : ContDiffOn ℝ 1 (hamiltonianVectorField (chi I)) univ)
    (hF : ∀ z, ‖hamiltonianVectorField (chi I) z‖ ≤ C * ‖z‖ ^ 3) {z : Phase 2}
    (hz : 32 * C * p11cQ_u z ≤ 1) :
    p11c_flow chi I 0 z = z ∧
    IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1) (fun t => p11c_flow chi I t z) ∧
    ∀ t ∈ Icc (-1 : ℝ) 1, p11cQ_u (p11c_flow chi I t z) ≤ 2 * p11cQ_u z := by
  obtain ⟨g, hg, hg0, hgu⟩ := p11cQ_exists hC hF1 hF hz
  have heq := p11cQ_flow_eq hF1 hg hg0
  have hex : ∃ g : ℝ → Phase 2,
      IsSolutionIn (hamiltonianVectorField (chi I)) univ (Icc (-1) 1) g ∧ g 0 = z := ⟨g, hg, hg0⟩
  have hfun : (fun t => p11c_flow chi I t z) = hex.choose := by
    funext t; unfold p11c_flow; simp only [hex, ↓reduceDIte]
  refine ⟨by rw [heq 0 ⟨by norm_num, by norm_num⟩, hg0], ?_,
    fun t ht => by rw [heq t ht]; exact hgu t ht⟩
  rw [hfun]
  exact hex.choose_spec.1

end KAM.Planetary

end
