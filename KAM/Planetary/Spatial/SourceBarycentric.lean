/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Newton

/-!
# Source-facing spatial barycentric reconstruction maps (OD-11 (b))

Package LP-FREEZE7R (statement audit of draft 7, round 1, finding F1), `LP:MAIN L1 (100–108)`,
`d = 3`; track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The total maps `spatialBarycentricPositions` and `spatialBarycentricVelocities`
(`KAM/Planetary/Spatial/Newton.lean`) divide by `1 + μ Σ ν_i` and by `ν_i`; on their whole Lean
carriers they include zero-denominator inputs outside the source (MAIN L1 takes positive `ν`, `μ`).
The source-facing maps below take the source premises `0 < ν_i` and `0 < μ` as proof arguments
and are definitionally the total maps (the `_def` equations are `rfl`). No characterization is
proposed: the implementation proves no barycentric identity (zero mass-weighted position sum,
`p_i = ν_i V_i`) for these maps, and MAIN L1 (100–106) gives the reconstruction by these explicit
formulas (`CHARACTERIZATION: N/A_LITERAL`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

def spatialSourceBarycentricPositions {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (_hν : ∀ i, 0 < ν i) (_hμ : 0 < μ) (q : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) := spatialBarycentricPositions ν μ q

def spatialSourceBarycentricVelocities {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (_hν : ∀ i, 0 < ν i) (_hμ : 0 < μ) (p : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) := spatialBarycentricVelocities ν μ p

theorem spatialSourceBarycentricPositions_def {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (hν : ∀ i, 0 < ν i) (hμ : 0 < μ) (q : Fin (n * 3) → ℝ) :
    spatialSourceBarycentricPositions ν μ hν hμ q = spatialBarycentricPositions ν μ q := rfl

theorem spatialSourceBarycentricVelocities_def {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (hν : ∀ i, 0 < ν i) (hμ : 0 < μ) (p : Fin (n * 3) → ℝ) :
    spatialSourceBarycentricVelocities ν μ hν hμ p = spatialBarycentricVelocities ν μ p := rfl

end KAM.Planetary.Spatial

end
