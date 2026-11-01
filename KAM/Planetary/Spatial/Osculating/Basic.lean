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

/-!
# Actual-velocity osculating elements in dimension three: definitions, velocity, tangency

Package LP-SP-OSC, `LP:MAIN L16 (508–529)` with `d = 3` and amendment N10; track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

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

/-- The actual heliocentric velocity `V_i = p_i/ν_i + μ ∑_j p_j` (`LP:MAIN (10)`, `L16`, `d = 3`).
-/
def spatialOscVelocity (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  (1 / ν i) • bodyVector3 z.2 i + μ • ∑ j, bodyVector3 z.2 j

/-- The gravitational parameter `k_i = 1 + μ ν_i`. -/
def spatialOscParam (ν : Fin n → ℝ) (μ : ℝ) (i : Fin n) : ℝ := 1 + μ * ν i

/-- `E_i^osc = |V_i|²/2 - k_i/|q_i|` (`LP:MAIN L16 (42)`). -/
def spatialOscEnergy (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spaceSq (spatialOscVelocity ν μ z i) / 2 -
    spatialOscParam ν μ i / spaceLength (bodyVector3 z.1 i)

/-- `a_i^osc = -k_i/(2 E_i^osc)` (`LP:MAIN L16 (42)`). -/
def spatialOscAxis (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  -spatialOscParam ν μ i / (2 * spatialOscEnergy ν μ z i)

/-- `𝐞_i^osc = ((|V_i|² - k_i/|q_i|) q_i - (q_i·V_i) V_i)/k_i` (`LP:MAIN L16 (42)`). -/
def spatialOscEccVector (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  (1 / spatialOscParam ν μ i) •
    ((spaceSq (spatialOscVelocity ν μ z i) -
        spatialOscParam ν μ i / spaceLength (bodyVector3 z.1 i)) • bodyVector3 z.1 i -
      spaceDot (bodyVector3 z.1 i) (spatialOscVelocity ν μ z i) • spatialOscVelocity ν μ z i)

/-- `e_i^osc = |𝐞_i^osc|` (`LP:MAIN L16 (42)`), Euclidean length. -/
def spatialOscEcc (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spaceLength (spatialOscEccVector ν μ z i)

/-- Osculating perihelion `a^osc (1 - e^osc)`. -/
def spatialOscPeri (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialOscAxis ν μ z i * (1 - spatialOscEcc ν μ z i)

/-- Osculating aphelion `a^osc (1 + e^osc)`. -/
def spatialOscApo (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialOscAxis ν μ z i * (1 + spatialOscEcc ν μ z i)

/-- Canonical perihelion `a_i (1 - e_i)`. -/
def spatialKeplerPeri (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialKeplerAxis ν z i * (1 - spaceLength (spatialKeplerEccVector ν z i))

/-- Canonical aphelion `a_i (1 + e_i)`. -/
def spatialKeplerApo (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spatialKeplerAxis ν z i * (1 + spaceLength (spatialKeplerEccVector ν z i))

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

theorem spatialOscAxis_eq_spec (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscAxis ν μ z i =
      spatialSpecAxis (spatialOscParam ν μ i) (bodyVector3 z.1 i)
        (spatialOscVelocity ν μ z i) := rfl

theorem spatialOscEccVector_eq_spec (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) (i : Fin n) :
    spatialOscEccVector ν μ z i =
      spatialSpecEccVector (spatialOscParam ν μ i) (bodyVector3 z.1 i)
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

/-- Valid actual-velocity osculating states (`LP:MAIN L16`, nondegenerate ellipses): positive
masses,
`μ > 0`, and for every planet `|q_i| > 0`, `E_i^osc < 0`, `e_i^osc < 1`. -/
abbrev SpatialOscPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 3) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialOscEnergy ν μ z i < 0 ∧
      spatialOscEcc ν μ z i < 1}

/-- `V_i` on the valid osculating carrier. -/
def spatialSourceOscVelocity {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) :
    Fin 3 → ℝ := spatialOscVelocity ν μ z.1 i

/-- `k_i` on the valid osculating carrier. -/
def spatialSourceOscParam {ν : Fin n → ℝ} {μ : ℝ} (_z : SpatialOscPhase n ν μ) (i : Fin n) : ℝ :=
  spatialOscParam ν μ i

/-- `E_i^osc` on the valid osculating carrier. -/
def spatialSourceOscEnergy {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) : ℝ :=
  spatialOscEnergy ν μ z.1 i

/-- `a_i^osc` on the valid osculating carrier. -/
def spatialSourceOscAxis {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) : ℝ :=
  spatialOscAxis ν μ z.1 i

/-- `𝐞_i^osc` on the valid osculating carrier. -/
def spatialSourceOscEccVector {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) :
    Fin 3 → ℝ := spatialOscEccVector ν μ z.1 i

/-- `e_i^osc` on the valid osculating carrier. -/
def spatialSourceOscEcc {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) : ℝ :=
  spatialOscEcc ν μ z.1 i

/-- `a^osc (1 - e^osc)` on the valid osculating carrier. -/
def spatialSourceOscPeri {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) : ℝ :=
  spatialOscPeri ν μ z.1 i

/-- `a^osc (1 + e^osc)` on the valid osculating carrier. -/
def spatialSourceOscApo {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ) (i : Fin n) : ℝ :=
  spatialOscApo ν μ z.1 i

/-- `a (1 - e)` on the canonical negative-energy carrier. -/
def spatialSourceKeplerPeri {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) : ℝ :=
  spatialKeplerPeri ν z.1 i

/-- `a (1 + e)` on the canonical negative-energy carrier. -/
def spatialSourceKeplerApo {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) : ℝ :=
  spatialKeplerApo ν z.1 i

/-! Defining equations of the carrier versions. -/

theorem spatialSourceOscVelocity_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscVelocity z i =
      (1 / ν i) • bodyVector3 z.1.2 i + μ • ∑ j, bodyVector3 z.1.2 j := rfl

theorem spatialSourceOscParam_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscParam z i = 1 + μ * ν i := rfl

theorem spatialSourceOscEnergy_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscEnergy z i =
      spaceSq (spatialSourceOscVelocity z i) / 2 -
        spatialSourceOscParam z i / spaceLength (bodyVector3 z.1.1 i) := rfl

theorem spatialSourceOscAxis_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscAxis z i =
      -spatialSourceOscParam z i / (2 * spatialSourceOscEnergy z i) := rfl

theorem spatialSourceOscEccVector_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscEccVector z i =
      (1 / spatialSourceOscParam z i) •
        ((spaceSq (spatialSourceOscVelocity z i) -
            spatialSourceOscParam z i / spaceLength (bodyVector3 z.1.1 i)) •
            bodyVector3 z.1.1 i -
          spaceDot (bodyVector3 z.1.1 i) (spatialSourceOscVelocity z i) •
            spatialSourceOscVelocity z i) := rfl

theorem spatialSourceOscEcc_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscEcc z i = spaceLength (spatialSourceOscEccVector z i) := rfl

theorem spatialSourceOscPeri_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscPeri z i =
      spatialSourceOscAxis z i * (1 - spatialSourceOscEcc z i) := rfl

theorem spatialSourceOscApo_eq {ν : Fin n → ℝ} {μ : ℝ} (z : SpatialOscPhase n ν μ)
    (i : Fin n) : spatialSourceOscApo z i =
      spatialSourceOscAxis z i * (1 + spatialSourceOscEcc z i) := rfl

theorem spatialSourceKeplerPeri_eq {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) :
    spatialSourceKeplerPeri z i =
      spatialKeplerAxis ν z.1 i * (1 - spaceLength (spatialKeplerEccVector ν z.1 i)) := rfl

theorem spatialSourceKeplerApo_eq {ν : Fin n → ℝ} (z : SpatialElliptic ν) (i : Fin n) :
    spatialSourceKeplerApo z i =
      spatialKeplerAxis ν z.1 i * (1 + spaceLength (spatialKeplerEccVector ν z.1 i)) := rfl

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
