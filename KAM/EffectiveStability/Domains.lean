/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import KAM.ODE.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Domains of the effective-stability chart dynamics (track B)

Cylinders (torus coordinates) and oscillator domains (Cartesian coordinates), their openness,
compactness and thickening inclusions, and the smooth observable `oscAct`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

variable {n : ℕ}

/-- Open cylinder `{w | ∀ j, |w.2 j| < c j}`. -/
def cyl (c : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {w | ∀ j, |w.2 j| < c j}

/-- Closed cylinder. -/
def cylClosed (c : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {w | ∀ j, |w.2 j| ≤ c j}

/-- Open action box. -/
def actionBox (c : Fin n → ℝ) : Set (Fin n → ℝ) := {J | ∀ j, |J j| < c j}

/-- Closed action box. -/
def actionBoxClosed (c : Fin n → ℝ) : Set (Fin n → ℝ) := {J | ∀ j, |J j| ≤ c j}

/-- Open oscillator domain. -/
def osc (c : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j < c j}

/-- Closed oscillator domain. -/
def oscClosed (c : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {w | ∀ j, KAM.Planetary.oscillatorAction w.2 w.1 j ≤ c j}

/-- The oscillator actions as a function of the phase point `w = (q, p)`. -/
def oscAct (w : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ := KAM.Planetary.oscillatorAction w.2 w.1

theorem oscAct_apply (w : (Fin n → ℝ) × (Fin n → ℝ)) (j : Fin n) :
    oscAct w j = (w.2 j ^ 2 + w.1 j ^ 2) / 2 := rfl

theorem oscillatorAction_nonneg (p q : Fin n → ℝ) (j : Fin n) :
    0 ≤ KAM.Planetary.oscillatorAction p q j := by
  unfold KAM.Planetary.oscillatorAction; positivity

theorem isOpen_actionBox (c : Fin n → ℝ) : IsOpen (actionBox c) := by
  have : actionBox c = ⋂ j, {J : Fin n → ℝ | |J j| < c j} := by ext; simp [actionBox]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_apply j).abs) continuous_const

theorem isOpen_cyl (c : Fin n → ℝ) : IsOpen (cyl c) := by
  have : cyl c = ⋂ j, {w : (Fin n → ℝ) × (Fin n → ℝ) | |w.2 j| < c j} := by ext; simp [cyl]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (((continuous_apply j).comp continuous_snd).abs) continuous_const

theorem continuous_oscAct : Continuous (oscAct (n := n)) := by
  refine continuous_pi fun j => ?_
  simp only [oscAct_apply]
  fun_prop

theorem isOpen_osc (c : Fin n → ℝ) : IsOpen (osc c) := by
  have : osc c = ⋂ j, {w : (Fin n → ℝ) × (Fin n → ℝ) | oscAct w j < c j} := by ext; simp [osc, oscAct]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_apply j).comp continuous_oscAct) continuous_const

theorem cyl_eq_prod (c : Fin n → ℝ) : cyl c = univ ×ˢ actionBox c := by
  ext w; simp [cyl, actionBox]

theorem actionBoxClosed_eq_pi (c : Fin n → ℝ) :
    actionBoxClosed c = Set.pi univ fun j => Icc (-c j) (c j) := by
  ext J; simp only [actionBoxClosed, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Icc, abs_le]

theorem isCompact_actionBoxClosed (c : Fin n → ℝ) : IsCompact (actionBoxClosed c) := by
  rw [actionBoxClosed_eq_pi]; exact isCompact_univ_pi fun j => isCompact_Icc

theorem isCompact_oscClosed (c : Fin n → ℝ) : IsCompact (oscClosed c) := by
  have hsub : oscClosed c ⊆ actionBoxClosed (fun j => c j + 1) ×ˢ actionBoxClosed (fun j => c j + 1) := by
    intro w hw
    have key : ∀ j, ∀ x : ℝ, (x ^ 2 + 0) / 2 ≤ c j → |x| ≤ c j + 1 := fun j x hx => by
      nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    refine ⟨fun j => key j _ ?_, fun j => key j _ ?_⟩
    · have := hw j; simp only [KAM.Planetary.oscillatorAction] at this; nlinarith [sq_nonneg (w.2 j)]
    · have := hw j; simp only [KAM.Planetary.oscillatorAction] at this; nlinarith [sq_nonneg (w.1 j)]
  have hcl : IsClosed (oscClosed c) := by
    have : oscClosed c = ⋂ j, {w : (Fin n → ℝ) × (Fin n → ℝ) | oscAct w j ≤ c j} := by
      ext; simp [oscClosed, oscAct]
    rw [this]
    exact isClosed_iInter fun j => isClosed_le ((continuous_apply j).comp continuous_oscAct) continuous_const
  exact ((isCompact_actionBoxClosed _).prod (isCompact_actionBoxClosed _)).of_isClosed_subset hcl hsub

theorem actionBoxClosed_subset_actionBox {b : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε) :
    actionBoxClosed b ⊆ actionBox (fun j => b j + ε) :=
  fun _ h j => lt_of_le_of_lt (h j) (by linarith)

theorem cylClosed_subset_cyl {b : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε) :
    cylClosed b ⊆ cyl (fun j => b j + ε) :=
  fun _ h j => lt_of_le_of_lt (h j) (by linarith)

theorem oscClosed_subset_osc {b : Fin n → ℝ} {ε : ℝ} (hε : 0 < ε) :
    oscClosed b ⊆ osc (fun j => b j + ε) :=
  fun _ h j => lt_of_le_of_lt (h j) (by linarith)

theorem add_angleShift_mem_cyl {c : Fin n → ℝ} {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ cyl c)
    (k : Fin n → ℤ) : w + KAM.ODE.angleShift k ∈ cyl c := by
  intro j; simpa [KAM.ODE.angleShift] using hw j

theorem contDiff_oscAct : ContDiff ℝ ⊤ (oscAct (n := n)) := by
  refine contDiff_pi.2 fun j => ?_
  simp only [oscAct_apply]
  fun_prop

/-- The derivative of the oscillator actions, as a continuous linear map. -/
def oscActDeriv (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    w.1 j • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _)) +
      w.2 j • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ _ _))

theorem hasFDerivAt_oscAct (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasFDerivAt (oscAct (n := n)) (oscActDeriv w) w := by
  refine hasFDerivAt_pi'.2 fun j => ?_
  have h1 : HasFDerivAt (fun w : (Fin n → ℝ) × (Fin n → ℝ) => w.1 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))) w :=
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ)
      (Fin n → ℝ))).hasFDerivAt
  have h2 : HasFDerivAt (fun w : (Fin n → ℝ) × (Fin n → ℝ) => w.2 j)
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) w :=
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ)
      (Fin n → ℝ))).hasFDerivAt
  have := ((h2.mul h2).add (h1.mul h1)).const_mul (1 / 2 : ℝ)
  have e : (fun x : (Fin n → ℝ) × (Fin n → ℝ) => oscAct x j) =
      fun x => (1 / 2 : ℝ) * (x.2 j * x.2 j + x.1 j * x.1 j) := by
    funext x; simp only [oscAct_apply]; ring
  rw [e]
  refine this.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [oscActDeriv]
  ring

theorem fderiv_oscAct (w v : (Fin n → ℝ) × (Fin n → ℝ)) :
    fderiv ℝ (oscAct (n := n)) w v = fun j => w.1 j * v.1 j + w.2 j * v.2 j := by
  rw [(hasFDerivAt_oscAct w).fderiv]
  ext j; simp [oscActDeriv]

end KAM.EffectiveStability
