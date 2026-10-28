/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Secular spectrum: the sorted spectrum of a simple-spectrum Hermitian matrix

Blueprint P, Part 9 (`stepP:p9:la-ev`).  For a Hermitian matrix with injective eigenvalue list,
the increasing enumeration `sorted` is strictly monotone, and the characteristic polynomial is the
product of the linear factors at the sorted eigenvalues.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Sorted
variable {A : Mat n} (hA : A.IsHermitian)

/-- `sorted` is the eigenvalue list composed with a bijection of the index set. -/
lemma sorted_eq_eigenvalues_comp :
    ∃ τ : Fin n → Fin n, Function.Bijective τ ∧ ∀ j, sorted A hA j = hA.eigenvalues (τ j) := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨fun j => e (Fin.cast (Fintype.card_fin n).symm j.rev), ?_, fun j => ?_⟩
  · rw [← Finite.injective_iff_bijective]
    exact e.injective.comp ((Fin.cast_injective _).comp Fin.rev_injective)
  · simp [sorted, Matrix.IsHermitian.eigenvalues, e]

lemma sorted_monotone : Monotone (sorted A hA) := by
  intro i j hij
  have hrev : Fin.cast (Fintype.card_fin n).symm j.rev ≤ Fin.cast (Fintype.card_fin n).symm i.rev := by
    rw [Fin.le_def, Fin.val_cast, Fin.val_cast, ← Fin.le_def]
    exact Fin.rev_le_rev.2 hij
  exact hA.eigenvalues₀_antitone hrev

lemma sorted_strictMono (hinj : Function.Injective hA.eigenvalues) :
    StrictMono (sorted A hA) := by
  obtain ⟨τ, hτ, hs⟩ := sorted_eq_eigenvalues_comp hA
  refine (sorted_monotone hA).strictMono_of_injective ?_
  intro i j h
  rw [hs, hs] at h
  exact hτ.1 (hinj h)

lemma charpoly_eq_prod_sorted :
    A.charpoly = ∏ k, (X - C (sorted A hA k)) := by
  obtain ⟨τ, hτ, hs⟩ := sorted_eq_eigenvalues_comp hA
  have h := hA.charpoly_eq
  simp only [RCLike.ofReal_real_eq_id, id] at h
  rw [h]
  simp_rw [hs]
  exact (hτ.prod_comp (fun i => X - C (hA.eigenvalues i))).symm

end Sorted

end SecularSpectrum

end KAM.Planetary
