/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Thresholds
public import KAM.Planetary.Hamiltonian.Transport
public import KAM.Planetary.PG.Setting
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Strip.RealRestriction

/-!
# Quantitative weak KAM: input and family interface (P11C-Q0)

`QuantitativeInput` is the local projection of the source hypotheses A1--A4 (holomorphy,
reality, finite-type lower bound, derivative bounds, max-to-max Hessian bound), and
`QuantitativeFamily` is the output-only family of Diophantine Lipschitz tori.
`IsLatticeTorus` and `unitCube` are the existing upstream definitions (imported, not redefined);
`p11c_zeroGood` belongs to the `Zero` module (Q5).
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

def p11c_scalar {N : ℕ} (rho : ℕ) (w : (Fin N → ℝ) → Fin N → ℝ)
    (c y : Fin N → ℝ) : ℝ := (∑ i, c i * w y i) ^ rho

def p11c_realDomain {N : ℕ} (d : QuantitativeData N) : Set (Phase N) :=
  {z | realInclusion N z.2 ∈ actionNbhd d.K (2 * d.vartheta)}

def QuantitativeInput {N : ℕ} (d : QuantitativeData N) (h : (Fin N → ℂ) → ℂ)
    (f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ) : Prop :=
  let U := actionNbhd d.K (2 * d.vartheta)
  let V := {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta}
  DifferentiableOn ℂ h U ∧ DifferentiableOn ℂ f (complexStrip N d.s ×ˢ U) ∧
  (∀ z ∈ complexStrip N d.s ×ˢ U, ∀ k : Fin N → ℤ,
    f (z.1 + fun i => (k i : ℂ), z.2) = f z) ∧
  (∀ y : Fin N → ℝ, realInclusion N y ∈ U → (h (realInclusion N y)).im = 0) ∧
  (∀ z : Phase N, realInclusion₂ N z ∈ complexStrip N d.s ×ˢ U → (f (realInclusion₂ N z)).im = 0) ∧
  (∀ c : Fin N → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ y ∈ d.K,
    ∃ j ≤ d.mu, ∃ v : Fin N → ℝ, KAM.Nekhoroshev.euclid v = 1 ∧
      d.beta ≤ |iteratedFDeriv ℝ j (p11c_scalar d.rho (frequencyMap h) c) y (fun _ => v)|) ∧
  (∀ c : Fin N → ℝ, KAM.Nekhoroshev.euclid c = 1 → ∀ j : ℕ, 1 ≤ j → j ≤ d.mu + 1 →
    ∀ y ∈ V, ∀ v : Fin j → (Fin N → ℝ), (∀ i, KAM.Nekhoroshev.euclid (v i) ≤ 1) →
      |iteratedFDeriv ℝ j (p11c_scalar d.rho (frequencyMap h) c) y v| ≤ d.M) ∧
  (∀ y ∈ U, ‖fderiv ℂ (fun x i => fderiv ℂ h x (Pi.single i 1)) y‖ ≤ d.C1) ∧
  (∀ j ≤ d.mu, ∀ y ∈ V, ∀ v : Fin N → ℝ, KAM.Nekhoroshev.euclid v = 1 →
    KAM.Nekhoroshev.euclid (iteratedFDeriv ℝ j (frequencyMap h) y (fun _ => v)) ≤ d.M0)

/-- Hessian is the max-to-max derivative of the complex gradient, as in A4. -/
def p11c_displacement {N : ℕ} (d : QuantitativeData N) (cDelta eps : ℝ) : ℝ :=
  min ((2 : ℝ) ^ (-18 : ℤ)) (cDelta * Real.sqrt eps / d.gamma)

structure QuantitativeFamily {N : ℕ} (d : QuantitativeData N) (H : Phase N → ℝ)
    (cDelta eps : ℝ) where
  good : Set (Fin N → ℝ)
  torus : (Fin N → ℝ) → (Fin N → ℝ) → Phase N
  freq : (Fin N → ℝ) → Fin N → ℝ
  compact : IsCompact good
  subset : good ⊆ d.K
  measure : volume d.K ≤ volume good + ENNReal.ofReal d.epsLoss
  lattice : ∀ b ∈ good, IsLatticeTorus angleShift H (p11c_realDomain d) (freq b) (torus b)
  dio : ∀ b ∈ good, IsDiophantine d.gamma d.tau (freq b)
  displacement : ∀ b ∈ good, ∀ θ, ‖torus b θ - (θ, b)‖ ≤ p11c_displacement d cDelta eps
  lower : ∀ b ∈ good, ∀ b' ∈ good, ∀ θ θ',
    (1 - (2 : ℝ) ^ (-10 : ℤ)) * ‖(θ, b) - (θ', b')‖ ≤ ‖torus b θ - torus b' θ'‖
  upper : ∀ b ∈ good, ∀ b' ∈ good, ∀ θ θ',
    ‖torus b θ - torus b' θ'‖ ≤ (1 + (2 : ℝ) ^ (-10 : ℤ)) * ‖(θ, b) - (θ', b')‖
  borel : MeasurableSet ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good))
  cell_lower : ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * volume good ≤
    volume ((fun z : Phase N => torus z.2 z.1) '' (unitCube N ×ˢ good))
  compact_closed : IsCompact ((fun z : Phase N => torus z.2 z.1) ''
    ((Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ good))

end KAM.Planetary
