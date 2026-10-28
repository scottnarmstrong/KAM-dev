/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorSetting

/-!
# P Parts 2-3: the joint source hypotheses of oscillator averaging (`bpP:p2:osc-averaging`)

`OscHyp` is copied verbatim from the design signatures (`P23Signatures.lean`); it contains only
literal source assumptions and typing/positivity data.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, packages P23-06 and P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Joint source hypotheses for oscillator averaging. -/
structure OscHyp {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq sbar s K α E : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : Prop where
  n_pos : 1 ≤ n
  m_pos : 1 ≤ m
  positive : 0 < r ∧ 0 < rp ∧ 0 < rq ∧ 0 < s ∧ 0 < K ∧ 0 < α
  sbar_nonneg : 0 ≤ sbar
  E_nonneg : 0 ≤ E
  budget : 6 ≤ 2 * π * K * s
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D r)
  real_h : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r →
    (h (KAM.realInclusion n I)).im = 0
  cls : oscClass D r rp rq (sbar + s) f
  bound : oscBound D r rp rq (sbar + s) f E
  real_f : RealOn (oscDom D r rp rq (sbar + s)) f
  divisor : DivisorBound (KAM.actionNbhd D r) K {0} h α
  small : 2 ^ 12 * (1 + (m : ℝ)) * K * E * s ≤ α * min (r * s) (rp * rq)

end KAM.Planetary

end
