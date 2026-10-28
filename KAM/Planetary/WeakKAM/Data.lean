/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Kepler.Basic
public import KAM.Canonical.Setting
public import KAM.Fourier.ExpSums
public import KAM.Strip.Limits
public import KAM.Measure.McShane
public import KAM.Measure.Lipeo
public import KAM.Measure.Lipschitz

/-! # P11B weak-KAM selection data

Carriers, explicit Euclidean seminorm helpers, the standing input structure `SelectionData`
(`sel-data`) and the separate perturbation premises `SelectionPerturbation`. No construction
output and no perturbation appear in `SelectionData`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

abbrev SelectionR (n : ℕ) := Fin n → ℝ
abbrev SelectionC (n : ℕ) := Fin n → ℂ
abbrev SelectionPhaseC (n : ℕ) := SelectionC n × SelectionC n
abbrev SelectionPoint (n : ℕ) := SelectionPhaseC n × SelectionC n

def selectionReal (x : SelectionR n) : SelectionC n := fun i => (x i : ℂ)
def selectionRe (x : SelectionC n) : SelectionR n := fun i => (x i).re
def selectionLength (x : SelectionR n) : ℝ := Real.sqrt (∑ i, x i ^ 2)
def selectionThick (K : Set (SelectionR n)) (v : ℝ) : Set (SelectionR n) :=
  {x | ∃ y ∈ K, selectionLength (x - y) ≤ v}
def selectionDomain (r s : ℝ) (B : Set (SelectionC n)) : Set (SelectionPoint n) :=
  {x | x.1.1 ∈ complexStrip n r ∧ ‖x.1.2‖ < s ∧ x.2 ∈ B}
def selectionScalar (ρ : ℕ) (ω : SelectionR n → SelectionR n)
    (c y : SelectionR n) : ℝ := (∑ i, c i * ω y i) ^ ρ
/-- Explicit Euclidean diagonal tensor seminorm; ambient Pi norm remains the max norm. -/
def selectionDG (j : ℕ) (g : SelectionR n → ℝ) (y : SelectionR n) : ℝ :=
  sSup {v | ∃ a : SelectionR n, selectionLength a = 1 ∧
    v = |iteratedFDeriv ℝ j g y (fun _ => a)|}
def selectionDGVector (j : ℕ) (g : SelectionR n → SelectionR n)
    (y : SelectionR n) : ℝ :=
  sSup {v | ∃ a : SelectionR n, selectionLength a = 1 ∧
    v = selectionLength (iteratedFDeriv ℝ j g y (fun _ => a))}

/-- Literal standing scalar/geometric inputs; no perturbation or construction outputs. -/
structure SelectionData (n : ℕ) where
  μ : ℕ
  ρ : ℕ
  τ : ℝ
  ϑ : ℝ
  strip : ℝ
  C₁ : ℝ
  β : ℝ
  M : ℝ
  loss : ℝ
  K : Set (SelectionR n)
  h : SelectionC n → ℂ
  n_pos : 1 ≤ n
  μ_pos : 1 ≤ μ
  rho_mem : ρ = 1 ∨ ρ = 2
  tau_nonneg : 0 ≤ τ
  tau_gap : (n : ℝ) * μ / ρ - 1 < τ
  compact : IsCompact K
  positive_measure : 0 < volume K
  theta_pos : 0 < ϑ
  theta_le : ϑ ≤ 1
  strip_pos : 0 < strip
  strip_le : strip ≤ 1
  hessian_normalized : 1 ≤ C₁
  beta_pos : 0 < β
  beta_le : β ≤ M
  loss_pos : 0 < loss
  loss_lt : ENNReal.ofReal loss < volume K
  holo : DifferentiableOn ℂ h (actionNbhd K (2 * ϑ))
  real : ∀ y : SelectionR n, selectionReal y ∈ actionNbhd K (2 * ϑ) →
    (h (selectionReal y)).im = 0
  hessian : ∀ b ∈ actionNbhd K (2 * ϑ),
    ‖fderiv ℂ (fun z i => fderiv ℂ h z (Pi.single i 1)) b‖ ≤ C₁
  finite_type : ∀ c : SelectionR n, selectionLength c = 1 → ∀ y ∈ K,
    ∃ j ≤ μ, β ≤ selectionDG j (selectionScalar ρ (frequencyMap h) c) y
  top_bounds : ∀ c : SelectionR n, selectionLength c = 1 → ∀ j : ℕ,
    1 ≤ j → j ≤ μ + 1 → ∀ y ∈ selectionThick K ϑ,
    ∀ a : Fin j → SelectionR n, (∀ i, selectionLength (a i) ≤ 1) →
    |iteratedFDeriv ℝ j (selectionScalar ρ (frequencyMap h) c) y a| ≤ M

/-- Perturbation premises, kept after the constants in every source theorem. -/
structure SelectionPerturbation (d : SelectionData n)
    (f : SelectionPhaseC n → ℂ) (ε : ℝ) : Prop where
  holo : DifferentiableOn ℂ f (complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ))
  periodic : ∀ z ∈ complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ),
    ∀ k : Fin n → ℤ, f (z.1 + (fun i => (k i : ℂ)), z.2) = f z
  real : ∀ z : Phase n, phaseToC z ∈
    complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ) → (f (phaseToC z)).im = 0
  bound : ∀ z ∈ complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ), ‖f z‖ ≤ ε

def sel_data (d : SelectionData n) := d

end KAM.Planetary
