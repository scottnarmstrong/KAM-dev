/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Newtonian.HamiltonNodes
public import KAM.Planetary.StrongAMD.Geometry
public import KAM.Planetary.StrongAMD.Continuation
public import KAM.Planetary.StrongAMD.Osculating.Estimates
public import KAM.Frozen.Planetary.StrongAMD.Defs.KeplerApo
public import KAM.Frozen.Planetary.StrongAMD.Defs.KeplerPeri
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscApo
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscAxis
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscEcc
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscEccVector
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscEnergy
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscParam
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscPeri
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscVelocity

/-!
# Actual-velocity osculating elements: definitions, velocity identification, tangency

Source: `LP:MAIN L16 (508–529)` with amendment N10; track LP, non-frozen.

Planar, literal `LP:MAIN L16 (42)`: for a phase `z` and planet `i` (`q_i`, `p_i` the body blocks),
`V_i = p_i/ν_i + μ ∑_j p_j`, `k_i = 1 + μ ν_i`, and the specific elements
`oscEnergy`, `oscAxis`, `oscEccVector`, `oscEcc`, `oscPeri`, `oscApo`.

* `oscVelocity_eq_movingField`: `V_i` is the `q_i`-block of the moving Hamiltonian field, i.e. the
  actual heliocentric velocity (`LP:MAIN (10)`, via `movingField_blocks`).
* `oscEnergy_eq_spec`, …: the elements are the generic `spec*` elements of `Estimates` with
  parameter `k_i`.
* `kepler*_eq_spec`: the canonical elements are the `spec*` elements with `k = 1` and
  `v_i = p_i/ν_i`; in particular `keplerEnergy ν z i = ν_i * specEnergy 1 q_i v_i`.
* `osc_tangency`: the osculating ellipse passes through `q_i` (Lemma 2 with parameter `k_i`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Kepler KAM.Planetary

variable {n : ℕ}

/-! ### The actual velocity is the `q`-block of the moving field -/

/-- `V_i = q̇_i`: on collision-free configurations, `oscVelocity` is the `q_i`-block of the
moving Hamiltonian field (`LP:MAIN (10)`; `movingField_blocks` with `G = m₀ = 1`). -/
theorem oscVelocity_eq_movingField (ν : Fin n → ℝ) (μ : ℝ) {z : Phase (n * 2)}
    (hz : NoCollision z.1) (i : Fin n) :
    bodyVector (movingField ν μ z).1 i = oscVelocity ν μ z i := by
  unfold movingField
  rw [(movingField_blocks 1 1 ν μ hz i).1]
  simp [oscVelocity, div_one]

/-! ### Identification with the generic elements -/

theorem oscEnergy_eq_spec (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) :
    oscEnergy ν μ z i =
      specEnergy (oscParam ν μ i) (bodyVector z.1 i) (oscVelocity ν μ z i) := rfl

theorem planeSq_smul_eq (c : ℝ) (v : Fin 2 → ℝ) : planeSq (c • v) = c ^ 2 * planeSq v := by
  simp only [planeSq_two, Pi.smul_apply, smul_eq_mul]; ring

theorem planeDot_smul_right_eq (c : ℝ) (v w : Fin 2 → ℝ) :
    planeDot v (c • w) = c * planeDot v w := by
  simp only [planeDot_two, Pi.smul_apply, smul_eq_mul]; ring

/-- The canonical total energy is `ν_i` times the specific energy of `v_i = p_i/ν_i`. -/
theorem keplerEnergy_eq_spec (ν : Fin n → ℝ) (z : Phase (n * 2)) {i : Fin n} (hν : ν i ≠ 0) :
    keplerEnergy ν z i =
      ν i * specEnergy 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) := by
  unfold keplerEnergy specEnergy
  rw [planeSq_smul_eq]
  field_simp

theorem keplerAxis_eq_spec (ν : Fin n → ℝ) (z : Phase (n * 2)) {i : Fin n} (hν : ν i ≠ 0) :
    keplerAxis ν z i =
      specAxis 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) := by
  unfold keplerAxis specAxis
  rw [keplerEnergy_eq_spec ν z hν, show 2 * (ν i * specEnergy 1 (bodyVector z.1 i)
    ((1 / ν i) • bodyVector z.2 i)) = ν i * (2 * specEnergy 1 (bodyVector z.1 i)
    ((1 / ν i) • bodyVector z.2 i)) by ring, neg_div, neg_div, div_mul_cancel_left₀ hν]
  simp only [one_div]

theorem keplerEccVector_eq_spec (ν : Fin n → ℝ) (z : Phase (n * 2)) {i : Fin n} (hν : ν i ≠ 0) :
    keplerEccVector ν z i =
      specEccVector 1 (bodyVector z.1 i) ((1 / ν i) • bodyVector z.2 i) := by
  unfold keplerEccVector specEccVector
  rw [planeSq_smul_eq, planeDot_smul_right_eq]
  ext c
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-! ### Tangency -/

/-- **Tangency** (`LP:MAIN L16 (527–528)`): the osculating ellipse passes through `q_i`, i.e.
`a^osc (1 - e^osc) ≤ |q_i| ≤ a^osc (1 + e^osc)` (Lemma 2 with parameter `k_i`; the ellipse is the
one with position `q_i`, velocity `V_i` and parameter `k_i`). -/
theorem osc_tangency (ν : Fin n → ℝ) {μ : ℝ} (hμ : 0 ≤ μ) {z : Phase (n * 2)} {i : Fin n}
    (hν : 0 < ν i) (hq : 0 < planeLength (bodyVector z.1 i)) (hE : oscEnergy ν μ z i < 0) :
    0 < oscAxis ν μ z i ∧ oscPeri ν μ z i ≤ planeLength (bodyVector z.1 i) ∧
      planeLength (bodyVector z.1 i) ≤ oscApo ν μ z i :=
  specAxis_tangency (by unfold oscParam; nlinarith [mul_nonneg hμ hν.le]) hq hE

end KAM.Planetary.StrongAMD

end
