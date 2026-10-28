/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Projections
public import KAM.Strip.RealRestriction
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Maximal canonical step: domains, admissibility and truncation (P11A-C0)

Source objects of `p11a2-cutoff-step.tex`: the domain `domain_def` (`bpP:p11a:domain-def`, built
from the existing `Weighted.Dom`), admissible functions, the sup bound `p11Bound`, the reality
predicate `p11Real`, the Fourier truncation `p11Cut`, the `eta`-Taylor part `p11Taylor` and the
cutoff `p11Cutoff`. The conventions `bpP:p11a:c2-conv#data` and `bpP:p11a:c2-conv#bracket` are
carried by the existing `Phase`, `actionNbhd` and `Canonical.poissonBracket`; no new aliases beyond
the carriers `P11CVec`/`P11Family` of `WeakMeasure/Basic` are introduced.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- The domain `D(r,s;B)`: angle strip of width `r`, action polydisc of radius `s`, parameters in
`B`. -/
def domain_def (n : ℕ) (r s : ℝ) (B : Set (P11CVec n)) : Set (P11Family n) :=
  KAM.Weighted.Dom n {0} s r ×ˢ B

/-- Admissible: holomorphic on `D(r,s;B)` and one-periodic in each angle. -/
def p11Admissible {n : ℕ} (r s : ℝ) (B : Set (P11CVec n)) (F : P11Family n → ℂ) : Prop :=
  DifferentiableOn ℂ F (domain_def n r s B) ∧
    ∀ j : Fin n, ∀ z ∈ domain_def n r s B,
      F ((z.1.1+Pi.single j 1,z.1.2),z.2)=F z

/-- Pointwise sup bound on a set. -/
def p11Bound {E F : Type*} [NormedAddCommGroup F] (U : Set E) (f : E → F) (M : ℝ) : Prop :=
  ∀ z ∈ U, ‖f z‖ ≤ M

/-- Reality guard: `F` is real-valued at the real points of `U`. -/
def p11Real {n : ℕ} (U : Set (P11Family n)) (F : P11Family n → ℂ) : Prop :=
  ∀ x : Phase n, ∀ b : P11Vec n,
    (KAM.realInclusion₂ n x,KAM.realInclusion n b) ∈ U →
      (F (KAM.realInclusion₂ n x,KAM.realInclusion n b)).im=0

/-- The truncation `cut_T F` in the angles, at fixed action and parameter. -/
def p11Cut {n : ℕ} (T : ℝ) (F : P11Family n → ℂ) (z : P11Family n) : ℂ :=
  KAM.Weighted.truncate T (fun u : P11CVec n × P11CVec n => F ((u.1,z.1.2),u.2))
    (z.1.1,z.2)

/-- First-order Taylor polynomial in the action at `eta = 0`. -/
def p11Taylor {n : ℕ} (F : P11Family n → ℂ) (z : P11Family n) : ℂ :=
  F ((z.1.1,0),z.2)+fderiv ℂ (fun eta => F ((z.1.1,eta),z.2)) 0 z.1.2

/-- Cutoff of the Taylor part. -/
def p11Cutoff {n : ℕ} (T : ℝ) (F : P11Family n → ℂ) := p11Cut T (p11Taylor F)

end KAM.Planetary
