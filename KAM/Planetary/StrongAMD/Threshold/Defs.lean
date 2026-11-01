/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Strong AMD thresholds: definitions

Package LP-THR, `LP:MAIN` §1 (lines 43–53), (3). Track LP, non-frozen; the statement surface is
proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The action chamber `chamber ν`, the axes `actionAxis ν I i = (I i / ν i)^2`, the eccentricity
deficit `D(u) = 1 - √(1 - u²)`, the feasible set of a pair, the pair objective and the pair
threshold `B_ij` (a literal `sInf`; its meaning as an attained minimum is the characterization
theorem of `KAM.Planetary.StrongAMD.Threshold.Pair`), and the cross, star and strong thresholds as
literal finite infima.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- `a_i(I) = (I_i / ν_i)²` (`LP:MAIN` §1 (45)). -/
def actionAxis (ν I : Fin n → ℝ) (i : Fin n) : ℝ := (I i / ν i) ^ 2

/-- The action chamber `𝒬 = {I : I_i > 0, a_1 < ⋯ < a_n}` (`LP:MAIN` §1 (43)). -/
def chamber (ν : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {I | (∀ i, 0 < I i) ∧ ∀ i j, i < j → actionAxis ν I i < actionAxis ν I j}

/-- The eccentricity deficit `D(u) = 1 - √(1 - u²)` (used on `u ∈ [0,1]`). -/
def eccDeficit (u : ℝ) : ℝ := 1 - Real.sqrt (1 - u ^ 2)

/-- The feasible set `{(u,v) ∈ [0,1]² : a_i(1+u) ≥ a_j(1-v)}` of the pair `(i,j)`. -/
def pairFeasible (ν I : Fin n → ℝ) (i j : Fin n) : Set (ℝ × ℝ) :=
  {uv | uv.1 ∈ Set.Icc (0 : ℝ) 1 ∧ uv.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    actionAxis ν I j * (1 - uv.2) ≤ actionAxis ν I i * (1 + uv.1)}

/-- The pair objective `I_i D(u) + I_j D(v)`. -/
def pairObjective (I : Fin n → ℝ) (i j : Fin n) (uv : ℝ × ℝ) : ℝ :=
  I i * eccDeficit uv.1 + I j * eccDeficit uv.2

/-- The pair threshold `B_ij(I)`, a literal `sInf` of the objective over the feasible set. -/
def pairThreshold (ν I : Fin n → ℝ) (i j : Fin n) : ℝ :=
  sInf (pairObjective I i j '' pairFeasible ν I i j)

/-- The index type of adjacent pairs `(i, i+1)` with `i + 1 < n`. -/
abbrev AdjIdx (n : ℕ) : Type := {i : Fin n // i.val + 1 < n}

/-- The upper index `i + 1` of an adjacent pair. -/
def AdjIdx.upperIdx (a : AdjIdx n) : Fin n := ⟨a.1.val + 1, a.2⟩

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

/-- The source carrier: action vectors in the chamber `𝒬`. -/
abbrev OrderedActions (ν : Fin n → ℝ) : Type := {I : Fin n → ℝ // I ∈ chamber ν}

/-- `B_ij` on the carrier `𝒬` (OD-2): the total helper `pairThreshold`, with the ordering
proof as typing data. -/
def orderedPairThreshold {ν : Fin n → ℝ} (I : OrderedActions ν) (i j : Fin n) (_hij : i < j) : ℝ :=
  pairThreshold ν I.1 i j

/-- `B_cross` on the carrier `𝒬` (OD-2); a literal infimum of carrier pair thresholds. -/
def orderedCrossThreshold {ν : Fin n → ℝ} (I : OrderedActions ν) : ℝ :=
  ⨅ a : AdjIdx n, orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx

/-- `B` on the carrier `𝒬` (OD-2), for `2 ≤ n` (the hypothesis is typing data). -/
def orderedStrongThreshold {ν : Fin n → ℝ} (_hn : 2 ≤ n) (I : OrderedActions ν) : ℝ :=
  min (orderedCrossThreshold I) (⨅ i : Fin n, I.1 i)

theorem orderedPairThreshold_eq {ν : Fin n → ℝ} (I : OrderedActions ν) (i j : Fin n)
    (hij : i < j) : orderedPairThreshold I i j hij = pairThreshold ν I.1 i j := rfl

theorem orderedStrongThreshold_eq {ν : Fin n → ℝ} (hn : 2 ≤ n) (I : OrderedActions ν) :
    orderedStrongThreshold hn I = strongThreshold ν I.1 := rfl

end KAM.Planetary.StrongAMD
