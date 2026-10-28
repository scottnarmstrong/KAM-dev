/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Norm
public import KAM.Planetary.Averaging.Setting
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip

/-!
# P Parts 2-3: the oscillator setting (`bpP:p2:s-osc#data`)

Flattening `oscPack` / `oscUnpack` of a phase `((θ, q), (I, p))` to the parameter `(θ, (I, p, q))`,
the transported function `oscFunction`, the parameter set `oscParams`, the domain `oscDom`, the
class `oscClass`, the weighted bound `oscBound` (evaluated with the existing `Weighted.coeff`,
`WSummable`, `wsum` at the flat parameter), the gauge `oscGauge`, and `s_osc_data`
(`oscUnpack ∘ oscPack = id`).
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-06.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-! Flat parameter order (I,p,q); phase order ((theta,q),(I,p)), frozen order. -/
def oscPack {n m : ℕ} (z : CPhase (n + m)) : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) :=
  (firstBlock (b := m) z.1, Fin.append (firstBlock (b := m) z.2)
    (Fin.append (lastBlock (a := n) z.2) (lastBlock (a := n) z.1)))
def oscUnpack {n m : ℕ} (z : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) : CPhase (n + m) :=
  (Fin.append z.1 (lastBlock (a := m) (lastBlock (a := n) z.2)),
    Fin.append (firstBlock (b := m + m) z.2) (firstBlock (b := m) (lastBlock (a := n) z.2)))
def oscFunction {n m : ℕ} (f : CHam (n + m)) :
    (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ := f ∘ oscUnpack

def oscParams {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq : ℝ) : Set (Fin (n + (m + m)) → ℂ) :=
  {x | firstBlock (b := m + m) x ∈ KAM.actionNbhd D r ∧
    ‖firstBlock (b := m) (lastBlock (a := n) x)‖ < rp ∧
    ‖lastBlock (a := m) (lastBlock (a := n) x)‖ < rq}
def oscDom {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) : Set (CPhase (n + m)) :=
  oscPack ⁻¹' (KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq)
def oscBound {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) (f : CHam (n + m)) (E : ℝ) : Prop :=
  ∀ x ∈ oscParams (m := m) D r rp rq,
    WSummable (oscFunction f) S x ∧ wsum (oscFunction f) S x ≤ E

def oscClass {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) (f : CHam (n + m)) : Prop :=
  DifferentiableOn ℂ f (oscDom D r rp rq S) ∧
    ∀ j : Fin n, ∀ z ∈ oscDom D r rp rq S,
      f (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) = f z

def oscGauge {n m : ℕ} (ρ ρp ρq σ : ℝ) (z : CPhase (n + m)) : ℝ :=
  max (max (‖firstBlock (b := m) z.1‖ / σ) (‖firstBlock (b := m) z.2‖ / ρ))
    (max (‖lastBlock (a := n) z.1‖ / ρq) (‖lastBlock (a := n) z.2‖ / ρp))

theorem s_osc_data {n m : ℕ} (z : CPhase (n + m)) : oscUnpack (oscPack z) = z := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
  simp only [oscUnpack, oscPack, firstBlock, lastBlock, Fin.append_left, Fin.append_right]

end KAM.Planetary

end
