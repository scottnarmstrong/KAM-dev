/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.RealRestriction
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Planetary.PG.Setting

/-!
# P Part 5: the extension data (`bpP:p5:ext`, definitions)

The complex phase carrier `PGComplexPhase`, `assembleComplex`, the thin domain `extensionDomain`
and the produced witness structure `PGExtension` (design revision 4: `agrees` only at real points
of the closed cylinder). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

abbrev PGComplexPhase (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)

def assembleComplex (I phi : Fin a → ℂ) (p q : Fin b → ℂ) : PGComplexPhase (a+b) :=
  (Fin.append phi q,Fin.append I p)

def extensionDomain (d : PGData a b) (delta : ℝ) : Set (PGComplexPhase (a+b)) :=
  {z | ∃ w : Phase (a+b), blockFast w.2 ∈ closure d.V ∧
    ‖(blockSlow w.2,blockSlow w.1)‖ ≤ d.r0/2 ∧ ‖z-KAM.realInclusion₂ (a+b) w‖ < delta}

/-- Produced witness, never an extra hypothesis of P-G. -/
structure PGExtension (d : PGData a b) where
  delta : ℝ
  MP : ℝ
  M0 : ℝ
  P : ℝ → PGComplexPhase (a+b) → ℂ
  H0 : (Fin a → ℂ) → ℂ
  delta_pos : 0 < delta
  delta_lt : delta < 1
  MP_pos : 0 < MP
  M0_pos : 0 < M0
  holo : ∀ mu ∈ Icc 0 d.mu0, DifferentiableOn ℂ (P mu) (extensionDomain d delta)
  continuous : ContinuousOn (fun z : ℝ × PGComplexPhase (a+b) => P z.1 z.2)
    (Icc 0 d.mu0 ×ˢ extensionDomain d delta)
  agrees : ∀ mu ∈ Icc 0 d.mu0, ∀ w : Phase (a+b), w ∈ closure (cylinder d.V d.r0) →
    KAM.realInclusion₂ (a+b) w ∈ extensionDomain d delta →
      P mu (KAM.realInclusion₂ (a+b) w) = (d.P mu w : ℂ)
  periodic : ∀ mu ∈ Icc 0 d.mu0, ∀ z ∈ extensionDomain d delta, ∀ k : Fin a → ℤ,
    P mu (z+KAM.realInclusion₂ (a+b) (fastShift k)) = P mu z
  bound : ∀ mu ∈ Icc 0 d.mu0, ∀ z ∈ extensionDomain d delta, ‖P mu z‖ ≤ MP
  h0holo : DifferentiableOn ℂ H0 (KAM.actionNbhd (closure d.V) delta)
  h0real : ∀ I : Fin a → ℝ, KAM.realInclusion a I ∈ KAM.actionNbhd (closure d.V) delta →
    H0 (KAM.realInclusion a I) = (d.H0 I : ℂ)
  h0bounds : ∀ I ∈ KAM.actionNbhd (closure d.V) delta,
    ‖H0 I‖ ≤ M0 ∧ ‖fderiv ℂ H0 I‖ ≤ M0 ∧ ‖fderiv ℂ (fderiv ℂ H0) I‖ ≤ M0

end KAM.Planetary

end
