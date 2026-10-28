/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationBase
public import KAM.Planetary.WeakKAM.IterationIncrement
public import KAM.Planetary.WeakKAM.IterationRetained

/-! # P11B iteration: the canonical-step hypotheses at stage `ν`

`stepChain` extends a chain by the data of one step, and `stage_hyp` verifies the hypotheses of
the canonical step (`stepP:p11a:il-c2`): the energy, frequency and remainder of stage `ν`
restricted to the collar `K_{ν+1} + t_{ν+1}`, the divisor on `K_{ν+1}` from the finite-stage
divisor lemma, and `‖Dω_ν‖ ≤ 2 C₁`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem phaseToC_eq_realInclusion₂ (z : Phase n) : phaseToC z = KAM.realInclusion₂ n z := by
  ext i <;> simp [phaseToC]

theorem domain_def_mono_B {r s : ℝ} {B B' : Set (P11CVec n)} (h : B' ⊆ B) :
    domain_def n r s B' ⊆ domain_def n r s B := fun _ hz => ⟨hz.1, h hz.2⟩

theorem p11Admissible_mono {r s : ℝ} {B B' : Set (P11CVec n)} {R : P11Family n → ℂ}
    (h : B' ⊆ B) (hR : p11Admissible r s B R) : p11Admissible r s B' R :=
  ⟨hR.1.mono (domain_def_mono_B h), fun j z hz => hR.2 j z (domain_def_mono_B h hz)⟩

theorem p11Bound_mono {r s M : ℝ} {B B' : Set (P11CVec n)} {R : P11Family n → ℂ}
    (h : B' ⊆ B) (hR : p11Bound (domain_def n r s B) R M) : p11Bound (domain_def n r s B') R M :=
  fun z hz => hR z (domain_def_mono_B h hz)

theorem p11Real_mono {r s : ℝ} {B B' : Set (P11CVec n)} {R : P11Family n → ℂ}
    (h : B' ⊆ B) (hR : p11Real (domain_def n r s B) R) : p11Real (domain_def n r s B') R :=
  fun x b hz => hR x b (domain_def_mono_B h hz)

theorem periodic_single_int (j : Fin n) :
    (fun i => (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℂ)) = (Pi.single j 1 : P11CVec n) := by
  ext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

section Pre
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
  {ch : SelectionChain n} {ν : ℕ} (hpre : IterPre d f a ch ν)
include hpre

theorem iterPre_admissible :
    p11Admissible (selectionr a ν) (selections a ν) (actionNbhd (ch.K ν) (selectiont a ν))
      (ch.R ν) ∧
    p11Bound (domain_def n (selectionr a ν) (selections a ν)
      (actionNbhd (ch.K ν) (selectiont a ν))) (ch.R ν) (selectionε a ν) ∧
    p11Real (domain_def n (selectionr a ν) (selections a ν)
      (actionNbhd (ch.K ν) (selectiont a ν))) (ch.R ν) := by
  have hm : ∀ z : P11Family n, z ∈ domain_def n (selectionr a ν) (selections a ν)
      (actionNbhd (ch.K ν) (selectiont a ν)) → z ∈ selectionDomain (selectionr a ν)
      (selections a ν) (actionNbhd (ch.K ν) (selectiont a ν)) := fun z hz => by
    rwa [selectionDomain_eq_domain_def]
  refine ⟨⟨?_, fun j z hz => ?_⟩, fun z hz => hpre.remainder_bound z (hm z hz), ?_⟩
  · have := hpre.remainder_holo
    rwa [selectionDomain_eq_domain_def] at this
  · have := hpre.remainder_periodic z (hm z hz) (Pi.single j 1)
    rwa [periodic_single_int] at this
  · intro x b hz
    have := hpre.remainder_real x b (by
      rw [phaseToC_eq_realInclusion₂, ← selectionReal_eq_realInclusion]
      rw [selectionReal_eq_realInclusion]
      exact hm _ hz)
    rwa [phaseToC_eq_realInclusion₂, selectionReal_eq_realInclusion] at this

end Pre

end KAM.Planetary

end
