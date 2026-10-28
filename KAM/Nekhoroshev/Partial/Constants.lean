/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Norm
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Strip.Analytic
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Frozen.Nekhoroshev.Defs.PartialTimeExponent
public import KAM.Frozen.Nekhoroshev.Defs.PartialDriftExponent
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Part 11 (N11-B): the source data, the numerical constants and the exponents

`PartialData` bundles exactly the frozen source premises of the partial convex Nekhoroshev
theorem; `PartialConstants` carries the literal numerical formulas of Part 11a, independent of
`μ, P, C, z, t`; `DefiniteSign` is the selected source sign witness; `exponents` records the
elementary comparisons between the frozen exponents.
-/

@[expose] public noncomputable section
open Set Metric
open KAM.Weighted

namespace KAM.Nekhoroshev
variable {n k : ℕ}

theorem exponents (hn : 2 ≤ n) :
    0 < partialTimeExponent n ∧ partialTimeExponent n < partialDriftExponent n ∧
    2 * partialDriftExponent n < 1/(2*(n:ℝ)) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < 6 * (n : ℝ) ^ 2 - 3 * n + 14 := by nlinarith
  unfold partialTimeExponent partialDriftExponent
  refine ⟨by positivity, ?_, ?_⟩
  · exact div_lt_div_of_pos_right (by norm_num) hD
  · have hn0 : (0:ℝ) < 2 * n := by positivity
    rw [mul_div_assoc', div_lt_div_iff₀ hD hn0]
    nlinarith

/-- Numerical data, no hypotheses or conclusions hidden in this carrier. -/
structure PartialConstants where
  n : ℕ
  ρ : ℝ
  g : ℝ
  m : ℝ
  Mc : ℝ
namespace PartialConstants
def s (a : PartialConstants) := a.ρ / (4*Real.pi)
def m1 (a : PartialConstants) := a.m / (2*Real.pi)
def M1 (a : PartialConstants) := a.Mc / (2*Real.pi)
def g1 (a : PartialConstants) := a.g / (2*Real.pi)
def r0 (a : PartialConstants) := min (a.ρ/2) (32*a.g/a.m)
def A (a : PartialConstants) := 40*a.Mc/a.m
def eps0 (a : PartialConstants) := a.m1*a.r0^2 / ((2:ℝ)^14*a.A^(2*a.n))
def R0 (a : PartialConstants) := a.r0/a.A
def kappaC (a : PartialConstants) := coth (Real.pi*a.s)^a.n
def cK (a : PartialConstants) := (2*Real.pi*a.eps0/a.kappaC) ^ (1/(2*(a.n:ℝ)))
def eps (a : PartialConstants) (μ : ℝ) := a.kappaC*μ/(2*Real.pi)
def K (a : PartialConstants) (μ : ℝ) := (a.eps0/a.eps μ) ^ (1/(2*(a.n:ℝ)))
def d (a : PartialConstants) (μ : ℝ) := μ ^ partialDriftExponent a.n
def kappa (a : PartialConstants) (μ : ℝ) := 2*Real.pi*a.K μ*a.s/Real.sqrt a.n
def rTheta (a : PartialConstants) (μ : ℝ) := a.r0/(a.A*a.K μ)^a.n
def blockTime (a : PartialConstants) (μ : ℝ) :=
  a.s*a.m1*a.rTheta μ/(240*a.M1*a.eps μ)*Real.exp (a.kappa μ/6)
end PartialConstants

/-- Exactly the frozen source premises, bundled only for internal signatures. -/
structure PartialData (n k : ℕ) where
  G : Set (Fin n → ℝ)
  G' : Set (Fin n → ℝ)
  D : Set (KAM.Planetary.Phase k)
  ρ : ℝ
  g : ℝ
  m : ℝ
  Mc : ℝ
  h : (Fin n → ℂ) → ℂ
  hn : 2 ≤ n
  hk : 1 ≤ k
  hG : IsOpen G
  hGc : Convex ℝ G
  hG' : IsOpen G'
  hGc' : Convex ℝ G'
  hD : IsOpen D
  hρ : 0 < ρ
  hMc : 0 < Mc
  collar : ∀ I ∈ G, Metric.closedBall I ρ ⊆ G'
  hol : DifferentiableOn ℂ h (KAM.actionNbhd G' ρ)
  C2 : ContDiffOn ℂ 2 h (KAM.actionNbhd G' ρ)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd G' ρ →
    (h (KAM.realInclusion n I)).im = 0
  Hess : ∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mc
  definite : HasDefiniteFastPart G' ρ g m h

def constants (a : PartialData n k) : PartialConstants := ⟨n,a.ρ,a.g,a.m,a.Mc⟩

/-- Explicit selected sign is a source witness, not a convexity conclusion. -/
def DefiniteSign (a : PartialData n k) (σ : ℝ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
    a.g ≤ ‖KAM.frequencyMap a.h I‖ ∧ ∀ v : Fin n → ℝ,
      a.m*(∑ i, (v i)^2) ≤ σ*fderiv ℝ (fderiv ℝ (realPart a.h)) I v v

end KAM.Nekhoroshev
end
