/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationPred
public import KAM.Planetary.WeakKAM.IterationRecord

/-! # P11B iteration: coherent assembly

`selectionIteration_of_step`: a base prefix and a coherent one-step extension of every prefix
produce an infinite iteration. The chain is read off the sequence of prefixes, so that every
finite prefix is the one the successor step extended (no independent existential chains).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem ChainAgree.refl (ν : ℕ) (c : SelectionChain n) : ChainAgree ν c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem ChainAgree.trans {ν : ℕ} {c c' c'' : SelectionChain n} (h : ChainAgree ν c c')
    (h' : ChainAgree ν c' c'') : ChainAgree ν c c'' :=
  ⟨fun j hj => (h'.K j hj).trans (h.K j hj), fun j hj => (h'.R j hj).trans (h.R j hj),
    fun j hj => (h'.Δω j hj).trans (h.Δω j hj), fun j hj => (h'.Δh j hj).trans (h.Δh j hj),
    fun j hj => (h'.X j hj).trans (h.X j hj)⟩

theorem selectionIteration_of_step (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) (c₀ : SelectionChain n) (h0 : IterPrefix d f a c₀ 0)
    (hstep : ∀ (ν : ℕ) (c : SelectionChain n), IterPrefix d f a c ν →
      ∃ c' : SelectionChain n, ChainAgree ν c c' ∧ IterPrefix d f a c' (ν + 1)) :
    Nonempty (SelectionIteration d f a) := by
  let seq : (ν : ℕ) → {c : SelectionChain n // IterPrefix d f a c ν} := fun ν =>
    Nat.rec ⟨c₀, h0⟩ (fun ν p => ⟨Classical.choose (hstep ν p.1 p.2),
      (Classical.choose_spec (hstep ν p.1 p.2)).2⟩) ν
  have hag : ∀ ν, ChainAgree ν (seq ν).1 (seq (ν + 1)).1 := fun ν =>
    (Classical.choose_spec (hstep ν (seq ν).1 (seq ν).2)).1
  have hle : ∀ m m', m ≤ m' → ChainAgree m (seq m).1 (seq m').1 := by
    intro m m' h
    induction m', h using Nat.le_induction with
    | base => exact ChainAgree.refl _ _
    | succ m' hm ih => exact ih.trans ((hag m').mono hm)
  let F : SelectionChain n :=
    { K := fun j => (seq j).1.K j
      Δω := fun j => (seq (j + 1)).1.Δω j
      Δh := fun j => (seq (j + 1)).1.Δh j
      X := fun j => (seq (j + 1)).1.X j
      R := fun j => (seq j).1.R j }
  have hF : ∀ m, ChainAgree m (seq m).1 F := fun m =>
    ⟨fun j hj => ((hle j m hj).K j le_rfl).symm, fun j hj => ((hle j m hj).R j le_rfl).symm,
      fun j hj => ((hle (j + 1) m hj).Δω j (Nat.lt_succ_self j)).symm,
      fun j hj => ((hle (j + 1) m hj).Δh j (Nat.lt_succ_self j)).symm,
      fun j hj => ((hle (j + 1) m hj).X j (Nat.lt_succ_self j)).symm⟩
  have hP : ∀ m, IterPrefix d f a F m := fun m => (seq m).2.transfer (hF m)
  have hpre : ∀ ν, IterPre d f a F ν := fun ν => ((hP ν) ν le_rfl).1
  have hpost : ∀ ν, IterPost d a F ν := fun ν =>
    (((hP (ν + 1)) ν (Nat.le_succ ν)).2 (Nat.lt_succ_self ν))
  exact ⟨⟨F, fun ν => (hpre ν).chain,
    fun ν => (hpre ν).energy_holo,
    fun ν => (hpost ν).increment_holo,
    fun ν => (hpost ν).increment_real,
    fun ν => (hpost ν).energy_bound,
    fun ν => (hpre ν).frequency_derivative,
    fun ν => (hpre ν).remainder_holo,
    fun ν => (hpre ν).remainder_bound,
    fun ν => (hpre ν).remainder_periodic,
    fun ν => (hpre ν).remainder_real,
    fun ν => (hpre ν).normal_form,
    fun ν => (hpost ν).map_holo,
    fun ν => (hpost ν).map_domain,
    fun ν => (hpost ν).map_periodic,
    fun ν => (hpost ν).map_real,
    fun ν => (hpost ν).map_symplectic,
    fun ν => (hpost ν).map_angle_bound,
    fun ν => (hpost ν).map_action_bound,
    fun ν => (hpost ν).map_derivative_bound,
    fun ν => (hpost ν).map_parameter_bound,
    fun ν => (hpost ν).map_affine,
    fun ν => (hpost ν).map_injective,
    fun ν => (hpost ν).real_angle_derivative⟩⟩


end KAM.Planetary

end
