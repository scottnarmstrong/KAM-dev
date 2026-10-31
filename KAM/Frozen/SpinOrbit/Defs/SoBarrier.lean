/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import KAM.Frozen.SpinOrbit.Defs.SoField

/-!
# Frozen structure `KAM.SpinOrbit.SoBarrier`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and
D49). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- An invariant barrier graph `p = P(q, φ)` of the physical flow with values in `[lo, hi]`:
continuous, 1-periodic in both angles, and invariant (a solution on an interval that meets the
graph once stays on it). -/
structure SoBarrier (lo hi : ℝ) where
  P : ℝ → ℝ → ℝ
  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2
  periodic_q : ∀ q φ, P (q + 1) φ = P q φ
  periodic_φ : ∀ q φ, P q (φ + 1) = P q φ
  invariant : ∀ (J : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), J.OrdConnected →
    (∀ t ∈ J, HasDerivAt y (soField (y t)) t) →
    ∀ t₁ ∈ J, (y t₁).2.1 = P (y t₁).1 (y t₁).2.2 → ∀ t ∈ J, (y t).2.1 = P (y t).1 (y t).2.2
  lower : ∀ q φ, lo ≤ P q φ
  upper : ∀ q φ, P q φ ≤ hi

end KAM.SpinOrbit

end
