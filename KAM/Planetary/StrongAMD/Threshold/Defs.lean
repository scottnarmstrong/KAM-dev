/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.StrongAMD.Defs.ActionAxis
public import KAM.Frozen.Planetary.StrongAMD.Defs.AdjIdx
public import KAM.Frozen.Planetary.StrongAMD.Defs.AdjIdxUpperIdx
public import KAM.Frozen.Planetary.StrongAMD.Defs.Chamber
public import KAM.Frozen.Planetary.StrongAMD.Defs.EccDeficit
public import KAM.Frozen.Planetary.StrongAMD.Defs.OrderedActions
public import KAM.Frozen.Planetary.StrongAMD.Defs.OrderedCrossThreshold
public import KAM.Frozen.Planetary.StrongAMD.Defs.OrderedPairThreshold
public import KAM.Frozen.Planetary.StrongAMD.Defs.OrderedStrongThreshold
public import KAM.Frozen.Planetary.StrongAMD.Defs.PairFeasible
public import KAM.Frozen.Planetary.StrongAMD.Defs.PairObjective
public import KAM.Frozen.Planetary.StrongAMD.Defs.PairThreshold

/-!
# Strong AMD thresholds: definitions

Source: `LP:MAIN` §1 (lines 43–53), (3). Track LP, non-frozen.

The action chamber `chamber ν`, the axes `actionAxis ν I i = (I i / ν i)^2`, the eccentricity
deficit `D(u) = 1 - √(1 - u²)`, the feasible set of a pair, the pair objective and the pair
threshold `B_ij` (a literal `sInf`; its meaning as an attained minimum is the characterization
theorem of `KAM.Planetary.StrongAMD.Threshold.Pair`), and the cross, star and strong thresholds as
literal finite infima.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- `B_cross(I) = min_{i+1<n} B_{i,i+1}(I)`, a literal finite infimum (needs `2 ≤ n` to be a
minimum over a nonempty family). -/
def crossThreshold (ν I : Fin n → ℝ) : ℝ :=
  ⨅ a : AdjIdx n, pairThreshold ν I a.1 a.upperIdx

/-- `B_⋆(I) = min_i I_i` (needs `1 ≤ n`). -/
def starThreshold (I : Fin n → ℝ) : ℝ := ⨅ i : Fin n, I i

/-- `B(I) = min (B_cross(I), B_⋆(I))` (`LP:MAIN` (3), lines 47–53). -/
def strongThreshold (ν I : Fin n → ℝ) : ℝ := min (crossThreshold ν I) (starThreshold I)

theorem AdjIdx.lt_upperIdx (a : AdjIdx n) : a.1 < a.upperIdx := by
  show a.1.val < a.1.val + 1
  omega

theorem orderedStrongThreshold_eq {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    orderedStrongThreshold hn I = strongThreshold ν I.1 := rfl

end KAM.Planetary.StrongAMD
