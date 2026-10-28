/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.Setting
public import KAM.Planetary.TwoScale.Constants
public import KAM.Planetary.Hamiltonian.Diophantine

/-!
# Two-scale KAM: the source-premise predicate `KamHyp` (`bpP:p3:conv#data`, `bpP:p3b#kam-bounds`)

`realFreq`, `dioBase`, `omegaSet` and the hypothesis bundle `KamHyp` of Proposition 3 of the
source (P3a), split from `Step` so that later modules import only the setting. The bundle contains
only source premises, positivity and typing data. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`,
package P23-14.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def realFreq {n : ℕ} (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (freq h (KAM.realInclusion n I) i).re

def dioBase {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (h : (Fin (a + b) → ℂ) → ℂ)
    (p : ScaleData) : Set (Fin (a + b) → ℝ) :=
  D ∩ realFreq h ⁻¹' twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ

def omegaSet {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (h : (Fin (a + b) → ℂ) → ℂ)
    (p : ScaleData) : Set (Fin (a + b) → ℝ) :=
  realFreq h '' D ∩ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ

/-- Source bound on a derivative and its row restrictions, using CLM operator norms.
The inverse is supplied as a map, with a two-sided inverse law at each point. -/
structure KamHyp {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (sbar : ℝ) (p : ScaleData)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop where
  a_pos : 1 ≤ a
  b_pos : 1 ≤ b
  τ_gt : ((a + b : ℕ) : ℝ) < p.τ
  positive : 0 < p.γ₂ ∧ 0 < p.s ∧ 0 < p.ρ ∧ 0 < p.E ∧
    0 < p.M ∧ 0 < p.Mhat ∧ 0 < p.Mbar ∧ 0 < p.Mbar₁ ∧ 0 < p.Mbar₂
  gamma_order : p.γ₂ ≤ p.γ₁
  widths : 4 * p.s ≤ sbar ∧ sbar < 1
  normalized : p.Mhat ≤ p.M ∧ p.Mbar₁ ≤ p.Mbar ∧ p.Mbar₂ ≤ p.Mbar
  L_bound : initialL p.M p.Mhat p.Mbar ≤ p.L
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D p.ρ)
  real_h : RealOn (coefficientDom D p.ρ (sbar + p.s)) (fun z => h z.2)
  real_f : RealOn (coefficientDom D p.ρ (sbar + p.s)) f
  f_class : InClass (realBase D) p.ρ (geometricWidth (sbar + p.s)) f
  f_bound : WBound (realBase D) p.ρ (geometricWidth (sbar + p.s)) f p.E
  injective : Set.InjOn (freq h) (KAM.actionNbhd D p.ρ)
  hessian : ∀ I ∈ KAM.actionNbhd D p.ρ,
    ‖fderiv ℂ (freq h) I‖ ≤ p.M ∧
    (∀ v, ‖lastBlock (a := a) (fderiv ℂ (freq h) I v)‖ ≤ p.Mhat * ‖v‖) ∧
    ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ (freq h) I ∧
      ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ p.Mbar ∧
      (∀ v, ‖firstBlock (b := b) (A.symm v)‖ ≤ p.Mbar₁ * ‖v‖) ∧
      (∀ v, ‖lastBlock (a := a) (A.symm v)‖ ≤ p.Mbar₂ * ‖v‖)
  small : kamConstant (a + b) p.τ * eHat p < 1

end KAM.Planetary

end
