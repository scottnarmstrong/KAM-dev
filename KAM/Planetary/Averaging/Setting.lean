/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Domains
public import KAM.Weighted.Norm
public import KAM.Canonical.Setting
public import KAM.Nekhoroshev.NormalForm.Setting
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Strip.RealRestriction

/-!
# P Parts 2-3: the averaging setting (`bpP:p2:conv#data`)

Carrier abbreviations `CPhase`, `CHam`, the coefficient/geometric width dictionary
(`geometricWidth`, `realBase`, `coefficientDom`, `realTube`, `conv_data`), the block
adapters `firstBlock`, `lastBlock` (`block_bridge` identifies them with the frozen `fast`,
`slow`), the P2 divisor setting `setting`, the two-scale divisor predicate `TwoDiv`, and the
source-premise bundles `DirectHyp`, `AvgHyp`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-01. The bundles contain source
premises, positivity and typing data only.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

abbrev CPhase (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)
abbrev CHam (n : ℕ) := CPhase n → ℂ

def geometricWidth (σ : ℝ) : ℝ := σ / (2 * π)
def realBase {n : ℕ} (D : Set (Fin n → ℝ)) : Set (Fin n → ℂ) := KAM.realInclusion n '' D
-- The frozen actionNbhd is used directly; no second tube representation.
def coefficientDom {n : ℕ} (D : Set (Fin n → ℝ)) (r σ : ℝ) : Set (CPhase n) :=
  Dom n (realBase D) r (geometricWidth σ)
def realTube {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℝ) :=
  (KAM.realInclusion n) ⁻¹' KAM.actionNbhd D r

def firstBlock {a b : ℕ} {𝕜 : Type*} (x : Fin (a + b) → 𝕜) : Fin a → 𝕜 :=
  fun i => x (Fin.castAdd b i)
def lastBlock {a b : ℕ} {𝕜 : Type*} (x : Fin (a + b) → 𝕜) : Fin b → 𝕜 :=
  fun i => x (Fin.natAdd a i)

theorem block_bridge {a b : ℕ} (v : Fin (a + b) → ℝ) :
    firstBlock (b := b) v = fast v ∧ lastBlock (a := a) v = slow v := ⟨rfl, rfl⟩

theorem conv_data {n : ℕ} (D : Set (Fin n → ℝ)) (r σ : ℝ) :
    polyNbhd (realBase D) r = KAM.actionNbhd D r ∧
    coefficientDom D r σ = KAM.complexStrip n (σ / (2 * π)) ×ˢ KAM.actionNbhd D r := by
  have h : polyNbhd (realBase D) r = KAM.actionNbhd D r := by
    ext I
    simp only [polyNbhd, realBase, KAM.actionNbhd, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨J, hJ, rfl⟩, hlt⟩
      exact ⟨J, hJ, hlt⟩
    · rintro ⟨J, hJ, hlt⟩
      exact ⟨_, ⟨J, hJ, rfl⟩, hlt⟩
  exact ⟨h, by simp only [coefficientDom, Dom, h, geometricWidth]⟩

/-- P2 setting, the exact N direct-divisor predicate with arbitrary q >= 1. -/
abbrev setting {n : ℕ} (D : Set (Fin n → ℂ)) (r K α q : ℝ)
    (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  DivisorBound (polyNbhd D r) K Λ h (α / q)

/-- Source premises shared by direct homological solve and splitting. -/
structure DirectHyp {n : ℕ} (D : Set (Fin n → ℂ)) (r s K α q δ : ℝ)
    (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (f : CHam n) : Prop where
  r_pos : 0 < r
  s_pos : 0 < s
  K_nonneg : 0 ≤ K
  α_pos : 0 < α
  q_ge : 1 ≤ q
  δ_nonneg : 0 ≤ δ
  holo : DifferentiableOn ℂ h (polyNbhd D r)
  div : setting D r K α q Λ h
  cls : InClass D r s f
  bound : WBound D r s f δ

/-- Full-neighbourhood two-scale nonresonance, no derived Lipschitz premise. -/
def TwoDiv {a b : ℕ} (V : Set (Fin (a + b) → ℂ)) (K α₁ α₂ q : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) : Prop :=
  ∀ I ∈ V, ∀ k : Fin (a + b) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ K →
    (if firstBlock (b := b) k = 0 then α₂ else α₁) / q ≤ ‖dotC k (freq h I)‖

/-- Averaging premises; E is a numerical bound, fixed before cutoff selection. -/
structure AvgHyp {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (r sbar s K α₁ α₂ E : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop where
  r_pos : 0 < r
  sbar_nonneg : 0 ≤ sbar
  s_pos : 0 < s
  K_pos : 0 < K
  budget : 6 ≤ 2 * π * K * s
  α₂_pos : 0 < α₂
  α_order : α₂ ≤ α₁
  E_nonneg : 0 ≤ E
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D r)
  real_h : RealOn (Dom (a + b) (realBase D) r (sbar + s)) (fun z => h z.2)
  real_f : RealOn (Dom (a + b) (realBase D) r (sbar + s)) f
  cls : InClass (realBase D) r (sbar + s) f
  bound : WBound (realBase D) r (sbar + s) f E
  div : TwoDiv (KAM.actionNbhd D r) K α₁ α₂ 1 h
  small : E ≤ α₂ * r / (128 * K)

end KAM.Planetary

end
