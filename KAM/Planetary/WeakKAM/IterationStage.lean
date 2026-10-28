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

theorem selection_cast_single (j : Fin n) :
    (fun i => (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℂ)) = (Pi.single j 1 : P11CVec n) := by
  ext i
  by_cases h : i = j <;> simp [h]

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
    rwa [selection_cast_single] at this
  · intro x b hz
    have hz' : (phaseToC x, selectionReal b) ∈ selectionDomain (selectionr a ν)
        (selections a ν) (actionNbhd (ch.K ν) (selectiont a ν)) := by
      rw [phaseToC_eq_realInclusion₂, selectionReal_eq_realInclusion]
      exact hm _ hz
    have := hpre.remainder_real x b hz'
    rwa [phaseToC_eq_realInclusion₂, selectionReal_eq_realInclusion] at this

end Pre

/-- The step data at stage `ν`: `E = K_{ν+1}` (the retained set) with the stage parameters. -/
abbrev stageS (d : SelectionData n) (a : SelectionSchedule n) (ch : SelectionChain n) (ν : ℕ)
    (hf : StepFacts a d.C₁ ν) : P11Step n :=
  stageStep a d.C₁ ν (selectionRetained a d ch ν) hf

/-- The chain `ch` extended by the stage-`ν` data (`K_{ν+1}`, `Δω_ν`, `Δh_ν`, `X_ν`, `R_{ν+1}`). -/
def stepChain (d : SelectionData n) (a : SelectionSchedule n) (ch : SelectionChain n) (ν : ℕ)
    (hf : StepFacts a d.C₁ ν) : SelectionChain n where
  K := fun j => if j = ν + 1 then selectionRetained a d ch ν else ch.K j
  Δω := fun j => if j = ν then p11DeltaW (selectionT a ν) (ch.R ν) else ch.Δω j
  Δh := fun j => if j = ν then p11DeltaH (selectionT a ν) (ch.R ν) else ch.Δh j
  X := fun j => if j = ν then
    (fun b z => p11StepMap (stageS d a ch ν hf) (selectionFrequency d ch ν) (ch.R ν) (z, b))
    else ch.X j
  R := fun j => if j = ν + 1 then
    p11StepRemainder (stageS d a ch ν hf) (selectionEnergy ch ν) (selectionFrequency d ch ν)
      (ch.R ν) else ch.R j

section StepChain
variable {d : SelectionData n} {a : SelectionSchedule n} {ch : SelectionChain n} {ν : ℕ}
  (hf : StepFacts a d.C₁ ν)

theorem stepChain_agree : ChainAgree ν ch (stepChain d a ch ν hf) :=
  ⟨fun j hj => by simp [stepChain, show j ≠ ν + 1 by omega],
    fun j hj => by simp [stepChain, show j ≠ ν + 1 by omega],
    fun j hj => by simp [stepChain, show j ≠ ν by omega],
    fun j hj => by simp [stepChain, show j ≠ ν by omega],
    fun j hj => by simp [stepChain, show j ≠ ν by omega]⟩

@[simp] theorem stepChain_K_succ : (stepChain d a ch ν hf).K (ν + 1) = selectionRetained a d ch ν :=
  by simp [stepChain]

theorem stepChain_K_self : (stepChain d a ch ν hf).K ν = ch.K ν := by simp [stepChain]

@[simp] theorem stepChain_Δω_self :
    (stepChain d a ch ν hf).Δω ν = p11DeltaW (selectionT a ν) (ch.R ν) := by simp [stepChain]

@[simp] theorem stepChain_Δh_self :
    (stepChain d a ch ν hf).Δh ν = p11DeltaH (selectionT a ν) (ch.R ν) := by simp [stepChain]

theorem stepChain_X_self (b : SelectionC n) :
    (stepChain d a ch ν hf).X ν b = fun z =>
      p11StepMap (stageS d a ch ν hf) (selectionFrequency d ch ν) (ch.R ν) (z, b) := by
  simp [stepChain]

@[simp] theorem stepChain_R_succ : (stepChain d a ch ν hf).R (ν + 1) =
    p11StepRemainder (stageS d a ch ν hf) (selectionEnergy ch ν) (selectionFrequency d ch ν)
      (ch.R ν) := by simp [stepChain]

end StepChain

section StageHyp
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
  (c : WeakBudgetCtx d a)

include c in
theorem retained_collar_sub {ch : SelectionChain n} {ν : ℕ} :
    actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1)) ⊆
      actionNbhd (ch.K ν) (selectiont a ν) :=
  selectionCollar_mono (fun _ hb => hb.1) (iter_t_anti c (Nat.le_succ ν))

include c in
theorem stage_hyp {ch : SelectionChain n} {ν : ℕ} (hpre : IterPre d f a ch ν)
    (hf : StepFacts a d.C₁ ν) :
    P11StepHyp (stageS d a ch ν hf) (selectionEnergy ch ν) (selectionFrequency d ch ν)
      (ch.R ν) := by
  have hext := hpre.chain.toSelectionExtensionChain
  have hsub := retained_collar_sub c (ch := ch) (ν := ν)
  have h := c.hyp
  have hadm := iterPre_admissible hpre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hpre.energy_holo.mono hsub
  · exact (selection_frequency_differentiableOn c hext).mono hsub
  · intro b hb
    have := hpre.energy_real b (by rw [selectionReal_eq_realInclusion]; exact hsub hb)
    rwa [selectionReal_eq_realInclusion] at this
  · intro b hb i
    have := selection_frequency_real c hext (b := b)
      (by rw [selectionReal_eq_realInclusion]; exact hsub hb) i
    rwa [selectionReal_eq_realInclusion] at this
  · exact p11Admissible_mono hsub hadm.1
  · exact p11Bound_mono hsub hadm.2.1
  · exact fun b hb => hpre.frequency_derivative b (hsub hb)
  · intro b hb k hk hkT
    have hk0 : 0 < selectionModeLength k :=
      lt_of_lt_of_le zero_lt_one (KAM.Fourier.one_le_modeSize hk)
    have hfd := finite_divisor d a ch ν hpre.chain h.ht h.hT h.hτ h.hγ h.hs h.he
      (fun m _ => iter_tail c m) b hb k hk0 hkT
    show selectionD a ν ≤ ‖p11dotC k (selectionFrequency d ch ν (KAM.realInclusion n b))‖
    rw [← selectionReal_eq_realInclusion]
    exact hfd.2.trans hfd.1

end StageHyp

end KAM.Planetary

end
