/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.ToriField

/-! # P11B tori: the output record `SelectionTori` and `limit_torus`

The limit-torus theorem (`bpP:p11a:limit-torus`) for the adapted schedule: for every
`b ∈ K_∞` the evaluation `θ ↦ (θ, b) + defect b θ` is real analytic, invariant under the real
Hamiltonian field of `h + f` along `ω_*(b)` (steps `lt-field`, `lt-cov`, `lt-lim`), Lagrangian
(`lt-lag`), and an immersion and embedding with constant `1 - 2⁻¹¹` (`lt-emb`). The Diophantine
clause `lt-dio` is already part of the output record `diophantine`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

def selectionHamiltonian (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (z : Phase n) : ℝ := realHamiltonian d.h f z

structure SelectionTori (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionLimit d f a where
  analytic : ∀ b ∈ Kinf, AnalyticOnNhd ℝ (selectionEvaluation defect b) univ
  invariance : ∀ b ∈ Kinf, ∀ θ,
    fderiv ℝ (selectionEvaluation defect b) θ (ωstar b) =
      hamiltonianVectorField (selectionHamiltonian d f) (selectionEvaluation defect b θ)
  orbit : ∀ b ∈ Kinf, ∀ θ, ∀ t : ℝ,
    HasDerivAt (fun t => selectionEvaluation defect b (θ + t • ωstar b))
      (hamiltonianVectorField (selectionHamiltonian d f)
        (selectionEvaluation defect b (θ + t • ωstar b))) t
  lagrangian : ∀ b ∈ Kinf, ∀ θ v w,
    symplecticForm (fderiv ℝ (selectionEvaluation defect b) θ v)
      (fderiv ℝ (selectionEvaluation defect b) θ w) = 0
  immersion_bound : ∀ b ∈ Kinf, ∀ θ v,
    (1 - (2 : ℝ)⁻¹ ^ 11) * ‖v‖ ≤ ‖fderiv ℝ (selectionEvaluation defect b) θ v‖
  embedding_bound : ∀ b ∈ Kinf, ∀ θ θ',
    (1 - (2 : ℝ)⁻¹ ^ 11) * ‖θ - θ'‖ ≤
      ‖selectionEvaluation defect b θ - selectionEvaluation defect b θ'‖

theorem limit_torus (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionTori d f (selectionAdapted d ε)) := by
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  have cx := weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he'
  obtain ⟨L⟩ := limit_map d ε he hsmall f hf
  have hinv : ∀ b ∈ L.Kinf, ∀ θ,
      fderiv ℝ (selectionEvaluation L.defect b) θ (L.ωstar b) =
        hamiltonianVectorField (selectionHamiltonian d f) (selectionEvaluation L.defect b θ) :=
    fun b hb θ => tori_invariance_real cx L hf hb θ
  refine ⟨{ L with
    analytic := fun b hb => tori_analytic L hb
    invariance := hinv
    orbit := fun b hb θ t => by
      have hpath : HasDerivAt (fun t : ℝ => θ + t • L.ωstar b) (L.ωstar b) t := by
        simpa using ((hasDerivAt_id t).smul_const (L.ωstar b)).const_add θ
      have h := (tori_diffAt_eval L hb (θ + t • L.ωstar b)).hasFDerivAt.comp_hasDerivAt t hpath
      rw [hinv b hb] at h
      exact h
    lagrangian := fun b hb θ v w => tori_lagrangian L cx hb θ v w
    immersion_bound := fun b hb θ v => tori_immersion L hb θ v
    embedding_bound := fun b hb θ θ' => tori_embedding L hb θ θ' }⟩

end KAM.Planetary

end
