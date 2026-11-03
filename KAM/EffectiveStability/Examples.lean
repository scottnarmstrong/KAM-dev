/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Torus
public import KAM.EffectiveStability.Oscillator

/-!
# Analytic edge cases of the confinement theorems (track B)

* `torus_confinement_example`: the integrable Hamiltonian `N(J) = ∑ J_j²` in the identity chart,
  with `R = 0` and `η = 0`: the actions are constant on `[-T, T]` (any `T ≥ 0`, in particular `0`).
* `oscillator_confinement_example`: the harmonic oscillator started at the origin keeps zero action.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

/-- Integrable Hamiltonian in the identity chart: the actions are constant. -/
theorem torus_confinement_example {n : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (w₀ : (Fin n → ℝ) × (Fin n → ℝ)) (hw₀ : ∀ j, |w₀.2 j| ≤ 1) :
    ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = w₀ ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, |(z t).2 j - w₀.2 j| ≤ 0 := by
  obtain ⟨T₁, -, z, h0, -, -, hb⟩ := torus_confinement (n := n) (fun _ => 1) (fun _ => 2)
    (fun _ => 0) 1 T one_pos hT (fun _ => le_rfl) (fun j => by norm_num) Set.univ isOpen_univ
    (fun w => ∑ j, w.2 j ^ 2) (ContDiff.sum fun j _ => by fun_prop).contDiffOn
    id id contDiffOn_id (fun _ _ => trivial)
    (fun w _ u v => by simp) (fun _ _ => rfl) (fun J => ∑ j, J j ^ 2) (fun _ => 0)
    (differentiableOn_const _) (fun _ _ _ => rfl) (fun w _ => by simp)
    (fun w _ j => by simp) w₀ hw₀
  refine ⟨z, by simpa using h0, fun t ht j => ?_⟩
  have := (hb t ht).2 j
  simpa using this.1

/-- The harmonic oscillator started at the origin keeps zero action. -/
theorem oscillator_confinement_example {n : ℕ} (T : ℝ) (hT : 0 ≤ T) :
    ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = 0 ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, KAM.Planetary.oscillatorAction (z t).2 (z t).1 j = 0 := by
  obtain ⟨T₁, -, z, h0, -, -, hb⟩ := oscillator_confinement (n := n) (fun _ => 0) (fun _ => 1)
    (fun _ => 0) 1 T one_pos hT (fun _ => le_rfl) (fun j => by norm_num) Set.univ isOpen_univ
    (fun w => ∑ j, KAM.Planetary.oscillatorAction w.2 w.1 j)
    (ContDiff.sum fun j _ =>
      (contDiff_pi.1 ((contDiff_oscAct (n := n)).of_le le_top) j)).contDiffOn
    id id contDiffOn_id (fun _ _ => trivial)
    (fun w _ u v => by simp) (fun _ _ => rfl) (fun I => ∑ j, I j) (fun _ => 0)
    (differentiableOn_const _) (fun w _ => by simp) (fun w _ j => by simp) 0 (fun j => by simp
      [KAM.Planetary.oscillatorAction])
  refine ⟨z, by simpa using h0, fun t ht j => ?_⟩
  have := (hb t ht).2 j
  exact le_antisymm (by simpa using this.2) (oscillatorAction_nonneg _ _ _)

end KAM.EffectiveStability
