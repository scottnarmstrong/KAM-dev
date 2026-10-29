/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Data
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.FundamentalDomain
public import KAM.Frozen.Defs.KamCover

/-!
# The standing data of Part 4

Definitions only.

* `KAM.Head.Data` is the data of HEAD (`bp:p4:sec-data`) with the witness `L_h` of the
  nondegeneracy hypothesis; the fields are the frozen HEAD binders.
* `KAM.Head.Pert` holds the hypotheses of HEAD on the perturbation `f` and its size `ε`.
* `KAM.Head.Layer` is the boundary-layer hypothesis with witness `C_B`.
* `KAM.Head.HeadConclusion` and `KAM.Head.HeadQConclusion` are the conclusions of the frozen
  HEAD (`KAM.kam_positive_measure`) and HEAD-Q (`KAM.kam_positive_measure_qualitative`), verbatim.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Head

/-- The data of HEAD fixed in `bp:p4:sec-data` (blueprint L138–147), with the witness `L_h` of the
nondegeneracy hypothesis. The fields are the frozen HEAD binders verbatim. -/
structure Data {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ) :
    Prop where
  two_le : 2 ≤ n
  tau_gt : (n : ℝ) - 1 < τ
  s₀_pos : 0 < s₀
  r₀_pos : 0 < r₀
  isOpen : IsOpen B
  isBounded : Bornology.IsBounded B
  holo : DifferentiableOn ℂ h (actionNbhd B r₀)
  real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
    (h fun i => (I i : ℂ)).im = 0
  nondeg : ∀ I ∈ closure B, ∀ J ∈ closure B,
    ‖I - J‖ ≤ Lh * ‖frequencyMap h I - frequencyMap h J‖

/-- The hypotheses of HEAD on the perturbation `f` and its size `ε` (frozen text verbatim). -/
structure Pert {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (ε : ℝ) : Prop where
  holo : DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀)
  periodic : ∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
    f (z.1 + (fun i => (k i : ℂ)), z.2) = f z
  real : ∀ θ I : Fin n → ℝ,
    ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
    (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  bound : ∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε

/-- The boundary-layer hypothesis of HEAD with witness `C_B`. -/
def Layer {n : ℕ} (B : Set (Fin n → ℝ)) (CB : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → volume {I ∈ B | Metric.infDist I Bᶜ < δ} ≤ ENNReal.ofReal (CB * δ)

/-- The conclusion of the frozen HEAD (`KAM.kam_positive_measure`), verbatim. -/
def HeadConclusion {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
      DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
      (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
        f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
      (∀ θ I : Fin n → ℝ,
        ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
        (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
      (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
      volume (fundamentalDomain B \
          kamCover h f B r₀ τ (C * Real.sqrt ε)) ≤
        ENNReal.ofReal (C * ε ^ ((1 : ℝ) / 4))

/-- The conclusion of the frozen HEAD-Q (`KAM.kam_positive_measure_qualitative`), verbatim. -/
def HeadQConclusion {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
      DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
      (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
        f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
      (∀ θ I : Fin n → ℝ,
        ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
        (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
      (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
      volume (fundamentalDomain B \ kamCover h f B r₀ τ κ) ≤
        ENNReal.ofReal κ * volume (fundamentalDomain B)

end KAM.Head

end
