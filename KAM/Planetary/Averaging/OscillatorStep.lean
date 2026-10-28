/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorGen
public import KAM.Planetary.Averaging.OscillatorClassAlgebra
public import KAM.Planetary.Averaging.OscillatorFlowProps
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# P Part 2: the oscillator step (`bpP:p2:osc-iter`)

`oscStepMap` is the time-one map of the Hamiltonian flow of `oscGen` on the domain `𝒪`.
`osc_iter_core` proves every clause of `osc_iter` except the class, the weighted bound and the
reality of the new remainder `fp` (see the handoff: the Lie-series transfer is not yet done).
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

def oscStepMap {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S ρ ρp ρq σ K : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : CPhase (n + m) → CPhase (n + m) :=
  flow (KAM.hamiltonianVectorFieldℂ (oscGen K h f)) (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1

end KAM.Planetary

end
