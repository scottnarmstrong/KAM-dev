/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Field
public import KAM.Planetary.Spatial.Elements
public import KAM.Planetary.Spatial.Osculating.Estimates
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerApo
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerPeri
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscApo
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscAxis
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEcc
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEccVector
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEnergy
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscParam
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscPeri
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscPhase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialOscVelocity
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerApo
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerPeri
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscApo
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscAxis
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEcc
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEccVector
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEnergy
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscParam
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscPeri
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscVelocity

/-!
# Actual-velocity osculating elements in dimension three: definitions, velocity, tangency

Source: `LP:MAIN L16 (508–529)` with `d = 3` and amendment N10; track LP, non-frozen.

Literal `LP:MAIN L16 (42)` for a phase `z : Phase (n * 3)` and planet `i` (`q_i`, `p_i` the body
blocks): `V_i = p_i/ν_i + μ ∑_j p_j`, `k_i = 1 + μ ν_i`, and the specific elements
`spatialOscEnergy`, `spatialOscAxis`, `spatialOscEccVector`, `spatialOscEcc`, `spatialOscPeri`,
`spatialOscApo`.

* `spatialOscVelocity_eq_hamiltonianVectorField`: `V_i` is the `q_i`-block of the spatial moving
  Hamiltonian field (`LP:MAIN (10)`, via `bodyVector3_hamiltonianVectorField_spatial_fst`).
* `spatialOscEnergy_eq_spec`, …: the elements are the generic `spatialSpec*` elements with `k_i`.
* `spatialKepler*_eq_spec`: the canonical elements are the `spatialSpec*` elements with `k = 1` and
  `v_i = p_i/ν_i`.
* `spatialOsc_tangency`: the osculating ellipse passes through `q_i` (Lemma 2 with parameter `k_i`).
* OD-11 (b): the carrier subtype `SpatialOscPhase` of valid osculating states
  (`0 < |q_i|`, `E^osc_i < 0`, `e^osc_i < 1`) with the source-facing restrictions and their defining
  equations; likewise `spatialSourceKeplerPeri/Apo` on the canonical carrier `SpatialElliptic`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary

variable {n : ℕ}

/-! ### The actual velocity is the `q`-block of the spatial moving field -/

/-- `V_i = q̇_i`: on collision-free configurations, `spatialOscVelocity` is the `q_i`-block of the
Hamilton field of `spatialHamiltonian ν μ` (`LP:MAIN (10)`). -/
theorem spatialOscVelocity_eq_hamiltonianVectorField (ν : Fin n → ℝ) (μ : ℝ)
    {z : Phase (n * 3)} (hz : SpatialNoCollision z.1) (i : Fin n) :
    bodyVector3 (hamiltonianVectorField (spatialHamiltonian ν μ) z).1 i =
      spatialOscVelocity ν μ z i :=
  bodyVector3_hamiltonianVectorField_spatial_fst ν μ hz i

/-! ### Identification with the generic elements -/

theorem spatialOscEnergy_eq_spec (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscEnergy ν μ z i =
      spatialSpecEnergy (spatialOscParam ν μ i) (bodyVector3 z.1 i)
        (spatialOscVelocity ν μ z i) := rfl

theorem spaceSq_smul_scalar (c : ℝ) (v : Fin 3 → ℝ) : spaceSq (c • v) = c ^ 2 * spaceSq v := by
  simp only [spaceSq_def, Pi.smul_apply, smul_eq_mul]; ring

/-- The canonical total energy is `ν_i` times the specific energy of `v_i = p_i/ν_i`. -/
theorem spatialKeplerEnergy_eq_spec (ν : Fin n → ℝ) (z : Phase (n * 3)) {i : Fin n}
    (hν : ν i ≠ 0) :
    spatialKeplerEnergy ν z i =
      ν i * spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) := by
  unfold spatialKeplerEnergy spatialSpecEnergy
  rw [spaceSq_smul_scalar]
  field_simp

theorem spatialKeplerAxis_eq_spec (ν : Fin n → ℝ) (z : Phase (n * 3)) {i : Fin n}
    (hν : ν i ≠ 0) :
    spatialKeplerAxis ν z i =
      spatialSpecAxis 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) := by
  unfold spatialKeplerAxis spatialSpecAxis
  rw [spatialKeplerEnergy_eq_spec ν z hν,
    show 2 * (ν i * spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i)) =
      ν i * (2 * spatialSpecEnergy 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i)) by ring,
    neg_div, neg_div, div_mul_cancel_left₀ hν]
  simp only [one_div]

theorem spatialKeplerEccVector_eq_spec (ν : Fin n → ℝ) (z : Phase (n * 3)) {i : Fin n}
    (hν : ν i ≠ 0) :
    spatialKeplerEccVector ν z i =
      spatialSpecEccVector 1 (bodyVector3 z.1 i) ((1 / ν i) • bodyVector3 z.2 i) := by
  unfold spatialKeplerEccVector spatialSpecEccVector
  rw [spaceSq_smul_scalar, spaceDot_smul_right]
  ext c
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-! ### Tangency -/

/-- **Tangency** (`LP:MAIN L16 (527–528)`): the osculating ellipse passes through `q_i`, i.e.
`a^osc (1 - e^osc) ≤ |q_i| ≤ a^osc (1 + e^osc)` (Lemma 2 with parameter `k_i`). -/
theorem spatialOsc_tangency (ν : Fin n → ℝ) {μ : ℝ} (hμ : 0 ≤ μ) {z : Phase (n * 3)} {i : Fin n}
    (hν : 0 < ν i) (hq : 0 < spaceLength (bodyVector3 z.1 i))
    (hE : spatialOscEnergy ν μ z i < 0) :
    0 < spatialOscAxis ν μ z i ∧ spatialOscPeri ν μ z i ≤ spaceLength (bodyVector3 z.1 i) ∧
      spaceLength (bodyVector3 z.1 i) ≤ spatialOscApo ν μ z i :=
  spatialSpecAxis_tangency (by unfold spatialOscParam; nlinarith [mul_nonneg hμ hν.le]) hq hE

/-! ### The valid osculating carrier (OD-11 (b)) -/

/-! Defining equations of the carrier versions. -/

/-- **Ellipse validity on the carrier**: a valid osculating state has `0 < a^osc`,
`0 < a^osc (1 - e^osc)` and the ellipse passes through `q_i`. -/
theorem spatialOscPhase_ellipse {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) :
    0 < spatialSourceOscAxis z i ∧ 0 < spatialSourceOscPeri z i ∧
      spatialSourceOscPeri z i ≤ spaceLength (bodyVector3 z.1.1 i) ∧
      spaceLength (bodyVector3 z.1.1 i) ≤ spatialSourceOscApo z i := by
  obtain ⟨hν, hμ, h⟩ := z.2
  obtain ⟨hq, hE, he⟩ := h i
  obtain ⟨h1, h2, h3⟩ := spatialOsc_tangency ν hμ.le (hν i) hq hE
  exact ⟨h1, mul_pos h1 (sub_pos.2 he), h2, h3⟩

end KAM.Planetary.Spatial

end
