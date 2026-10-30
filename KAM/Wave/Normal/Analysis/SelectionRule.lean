/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.SineProducts
public import KAM.Wave.Normal.QuarticCoeff

/-!
# The selection rule for the quartic overlaps `g_{ijkl}`
(bridge to the landed W0-NORMAL `bpW:w0n:quartic-coeff`; used by `bpW:w0n:cubic-bound`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`waveQuartic` is `sineQuarticCoeff`, `waveSign` is `boolSign`, and
`KAM.Wave.abs_waveQuartic_le_signs` is `abs_quarticCoeff_le`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The sign `±1` attached to a Boolean (the landed `boolSign`). -/
abbrev waveSign (b : Bool) : ℤ := boolSign b

/-- `|g_{ijkl}| ≤ (1/2π) Σ_ε [l = ε₁ i + ε₂ j + ε₃ k]` (`bpW:w0n:g-signed`). -/
theorem abs_waveQuartic_le_signs (i j k l : ℕ+) :
    |waveQuartic i j k l| ≤ (1 / (2 * Real.pi)) * ∑ ε : Bool × Bool × Bool,
      (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((i : ℕ) : ℤ) + waveSign ε.2.1 * ((j : ℕ) : ℤ)
            + waveSign ε.2.2 * ((k : ℕ) : ℤ) then (1 : ℝ) else 0) :=
  abs_quarticCoeff_le i j k l

end KAM.Wave

end
