/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.MovingHamiltonian
public import KAM.Frozen.Planetary.StrongAMD.Defs.StrongAMD

/-!
# Reduced-mass Kepler elements are the frozen elements at the mass vector `redMass ν μ`

Scoping note `docs/tracks/LP/REDUCED-MASS-SCOPE.md` §0 (branch `lp-redmass-scope`), checked in Lean.
Additive core; non-frozen.

The Kepler summand of the moving-Sun Hamiltonian `movingHamiltonian 1 1 ν μ` is
`E^red_i = (1/ν_i + μ)|p_i|²/2 - ν_i/|q_i|` (`reducedKeplerEnergy`): the heliocentric Kepler energy
with the diagonal `μ|p_i|²/2` of the perturbation moved in. It is the energy of a Kepler problem
of mass `β_i = ν_i/(1 + μν_i)` (`reducedBeta`) about a centre of parameter `M_i = 1 + μν_i`
(`reducedCentral`): `E^red_i = |p_i|²/(2β_i) - β_i M_i/|q_i|` (`reducedKeplerEnergy_eq_kepler`).
Its elements are the semi-axis `a^red = -β M/(2E^red)`, the Delaunay action `Λ^red = β √(M a^red)`
and the Laplace–Runge–Lenz vector with coefficient `1/(β² M)`.

With `s_i = √(1 + μν_i)` and the reduced mass vector `ν'_i = ν_i / s_i` (`redMass`), the frozen
heliocentric elements at `ν'` are these reduced elements:

* `keplerEnergy_redMass`: `keplerEnergy ν' z i = E^red_i / s_i`;
* `keplerAxis_redMass`: `keplerAxis ν' z i = a^red_i = -ν_i/(2E^red_i)`;
* `keplerAction_redMass`: `keplerAction ν' z i = Λ^red_i`, the reduced Delaunay action;
* `keplerEccVector_redMass`: `keplerEccVector ν' z i` is the reduced eccentricity vector;
* `strongAMD_redMass`: `strongAMD ν' z = Σ Λ^red_i - |L|` (the total momentum is split-free).

No sign of the energy is needed: the identities hold for every state, both sides using Lean's
`x / 0 = 0` and `√x = 0` for `x ≤ 0` in the same way. The action identity is physically
meaningful only for a bound reduced orbit, `E^red_i < 0`, which `E_i < 0` does not imply
(`E^red_i = E_i + μ|p_i|²/2`); for `E^red_i ≥ 0` both sides are `0`.

Against the heliocentric elements: `E^red_i = E_i + μ|p_i|²/2` (`reducedKeplerEnergy_eq_add`) and,
for `E_i < 0`, `Λ^red_i = Λ_i √(E_i/E^red_i) / s_i` (`keplerAction_redMass_eq_mul`), the exact form
of the oscillation `G_i - Λ_i` (first order `μ ν_i Λ_i (a_i/|q_i| - 1)`, note §0).
-/

@[expose] public noncomputable section

open KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-! ### The reduced mass vector -/

/-- The reduced mass vector `ν'_i = ν_i / √(1 + μ ν_i)` (scoping note §0). -/
def redMass (ν : Fin n → ℝ) (μ : ℝ) : Fin n → ℝ := fun i => ν i / Real.sqrt (1 + μ * ν i)

theorem one_add_mul_pos {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {μ : ℝ} (hμ : 0 ≤ μ) (i : Fin n) :
    0 < 1 + μ * ν i := by
  have := mul_nonneg hμ (hν i).le
  linarith

theorem redMass_pos {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {μ : ℝ} (hμ : 0 ≤ μ) (i : Fin n) :
    0 < redMass ν μ i :=
  div_pos (hν i) (Real.sqrt_pos.2 (one_add_mul_pos hν hμ i))

theorem redMass_le {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {μ : ℝ} (hμ : 0 ≤ μ) (i : Fin n) :
    redMass ν μ i ≤ ν i := by
  have h1 : 1 ≤ Real.sqrt (1 + μ * ν i) := by
    rw [Real.one_le_sqrt]
    have := mul_nonneg hμ (hν i).le
    linarith
  exact div_le_self (hν i).le h1

@[simp] theorem redMass_zero (ν : Fin n → ℝ) : redMass ν 0 = ν := by
  funext i
  simp [redMass]

/-! ### The reduced Kepler problem -/

/-- The Kepler summand `E^red_i = (1/ν_i + μ)|p_i|²/2 - ν_i/|q_i|` of `movingHamiltonian 1 1 ν μ`
(`movingHamiltonian_eq_sum_reducedKeplerEnergy`). -/
def reducedKeplerEnergy (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  (1 / ν i + μ) * planeSq (bodyVector z.2 i) / 2 - ν i / planeLength (bodyVector z.1 i)

/-- `E^red_i` is the Kepler summand of the moving-Sun Hamiltonian at `G = m₀ = 1`: the
Hamiltonian is `Σ E^red_i` plus `μ` times the pair terms. -/
theorem movingHamiltonian_eq_sum_reducedKeplerEnergy (ν : Fin n → ℝ) (μ : ℝ)
    (z : Phase (n * 2)) :
    movingHamiltonian 1 1 ν μ z = ∑ i, reducedKeplerEnergy ν μ z i +
      μ * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (planeDot (bodyVector z.2 i) (bodyVector z.2 j) -
          ν i * ν j / planeLength (bodyVector z.1 i - bodyVector z.1 j)) := by
  simp [movingHamiltonian, reducedKeplerEnergy]

/-- The mass `β_i = ν_i / (1 + μ ν_i)` of the reduced Kepler problem. -/
def reducedBeta (ν : Fin n → ℝ) (μ : ℝ) (i : Fin n) : ℝ := ν i / (1 + μ * ν i)

/-- The central parameter `M_i = 1 + μ ν_i` of the reduced Kepler problem (`G m₀ = 1`). -/
def reducedCentral (ν : Fin n → ℝ) (μ : ℝ) (i : Fin n) : ℝ := 1 + μ * ν i

theorem reducedBeta_mul_reducedCentral {ν : Fin n → ℝ} {μ : ℝ} {i : Fin n}
    (hs : 0 < 1 + μ * ν i) : reducedBeta ν μ i * reducedCentral ν μ i = ν i := by
  unfold reducedBeta reducedCentral
  exact div_mul_cancel₀ _ hs.ne'

/-- `E^red_i` is the energy `|p|²/(2β) - βM/|q|` of the Kepler problem of mass `β_i` about a
centre of parameter `M_i`. -/
theorem reducedKeplerEnergy_eq_kepler {ν : Fin n → ℝ} {μ : ℝ} {i : Fin n} (hν : 0 < ν i)
    (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    reducedKeplerEnergy ν μ z i =
      planeSq (bodyVector z.2 i) / (2 * reducedBeta ν μ i) -
        reducedBeta ν μ i * reducedCentral ν μ i / planeLength (bodyVector z.1 i) := by
  rw [reducedBeta_mul_reducedCentral hs]
  unfold reducedKeplerEnergy reducedBeta
  congr 1
  field_simp

/-- The reduced semi-axis `a^red_i = -β_i M_i / (2 E^red_i)`. -/
def reducedKeplerAxis (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  -(reducedBeta ν μ i * reducedCentral ν μ i) / (2 * reducedKeplerEnergy ν μ z i)

/-- The reduced Delaunay action `Λ^red_i = β_i √(M_i a^red_i)`. -/
def reducedDelaunayAction (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : ℝ :=
  reducedBeta ν μ i * Real.sqrt (reducedCentral ν μ i * reducedKeplerAxis ν μ z i)

/-- The reduced Laplace–Runge–Lenz eccentricity vector
`(|p|²/(β² M) - 1/|q|) q - (q·p/(β² M)) p` of the reduced Kepler problem. -/
def reducedEccVector (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 2)) (i : Fin n) : Fin 2 → ℝ :=
  let q := bodyVector z.1 i
  let p := bodyVector z.2 i
  (planeSq p / (reducedBeta ν μ i ^ 2 * reducedCentral ν μ i) - 1 / planeLength q) • q -
    (planeDot q p / (reducedBeta ν μ i ^ 2 * reducedCentral ν μ i)) • p

/-! ### The frozen elements at `redMass ν μ` -/

section Identity

variable {ν : Fin n → ℝ} {μ : ℝ} {i : Fin n}

private theorem sqrt_sq_eq (hs : 0 < 1 + μ * ν i) :
    Real.sqrt (1 + μ * ν i) ^ 2 = 1 + μ * ν i :=
  Real.sq_sqrt hs.le

/-- **§0, energy:** `keplerEnergy ν' z i = E^red_i / s_i`, `s_i = √(1 + μ ν_i)`. -/
theorem keplerEnergy_redMass (hν : 0 < ν i) (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    keplerEnergy (redMass ν μ) z i = reducedKeplerEnergy ν μ z i / Real.sqrt (1 + μ * ν i) := by
  have hs' : 0 < Real.sqrt (1 + μ * ν i) := Real.sqrt_pos.2 hs
  have hsq := sqrt_sq_eq hs
  unfold keplerEnergy reducedKeplerEnergy redMass
  set s := Real.sqrt (1 + μ * ν i)
  set P := planeSq (bodyVector z.2 i)
  rw [div_eq_mul_inv (ν i / s), div_eq_mul_inv (ν i) (planeLength _)]
  set L := (planeLength (bodyVector z.1 i))⁻¹
  field_simp
  linear_combination P * hsq

/-- **§0, semi-axis:** `keplerAxis ν' z i = a^red_i` (`= -ν_i / (2 E^red_i)`). -/
theorem keplerAxis_redMass (hν : 0 < ν i) (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    keplerAxis (redMass ν μ) z i = reducedKeplerAxis ν μ z i := by
  have hs' : 0 < Real.sqrt (1 + μ * ν i) := Real.sqrt_pos.2 hs
  unfold keplerAxis reducedKeplerAxis
  rw [keplerEnergy_redMass hν hs, reducedBeta_mul_reducedCentral hs]
  unfold redMass
  set E := reducedKeplerEnergy ν μ z i
  set s := Real.sqrt (1 + μ * ν i)
  clear_value s
  rcases eq_or_ne E 0 with hE | hE
  · simp [hE]
  · field_simp

/-- `a^red_i = -ν_i / (2 E^red_i)`. -/
theorem reducedKeplerAxis_eq (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    reducedKeplerAxis ν μ z i = -ν i / (2 * reducedKeplerEnergy ν μ z i) := by
  unfold reducedKeplerAxis
  rw [reducedBeta_mul_reducedCentral hs]

/-- **§0, action:** `keplerAction ν' z i = Λ^red_i`, the reduced Delaunay action. -/
theorem keplerAction_redMass (hν : 0 < ν i) (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    keplerAction (redMass ν μ) z i = reducedDelaunayAction ν μ z i := by
  have hs' : 0 < Real.sqrt (1 + μ * ν i) := Real.sqrt_pos.2 hs
  have hsq := sqrt_sq_eq hs
  unfold keplerAction reducedDelaunayAction
  rw [keplerAxis_redMass hν hs]
  have hM : reducedCentral ν μ i = Real.sqrt (1 + μ * ν i) ^ 2 := by
    rw [hsq]; rfl
  rw [hM, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs'.le]
  unfold redMass reducedBeta
  set s := Real.sqrt (1 + μ * ν i)
  clear_value s
  rw [← hsq]
  field_simp

/-- **§0, eccentricity vector:** `keplerEccVector ν' z i` is the reduced eccentricity vector
(`ν'_i² = β_i² M_i`). -/
theorem keplerEccVector_redMass (hν : 0 < ν i) (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    keplerEccVector (redMass ν μ) z i = reducedEccVector ν μ z i := by
  have hsq := sqrt_sq_eq hs
  have hm : redMass ν μ i ^ 2 = reducedBeta ν μ i ^ 2 * reducedCentral ν μ i := by
    unfold redMass reducedBeta reducedCentral
    rw [div_pow, hsq]
    field_simp
  unfold keplerEccVector reducedEccVector
  simp only [hm]

/-- **§0, strong AMD:** at `ν'` the strong AMD is `Σ Λ^red_i - |L|` (the total momentum does not
depend on the split). -/
theorem strongAMD_redMass (hν : ∀ i, 0 < ν i) (hs : ∀ i, 0 < 1 + μ * ν i) (z : Phase (n * 2)) :
    strongAMD (redMass ν μ) z = (∑ i, reducedDelaunayAction ν μ z i) - |totalMomentum z| := by
  unfold strongAMD
  simp only [keplerAction_redMass (hν _) (hs _)]

/-! ### The reduced action against the heliocentric action -/

/-- `E^red_i = E_i + μ |p_i|² / 2`: the reduced energy is the heliocentric Kepler energy plus the
diagonal kinetic term of the perturbation. -/
theorem reducedKeplerEnergy_eq_add (hν : 0 < ν i) (z : Phase (n * 2)) :
    reducedKeplerEnergy ν μ z i = keplerEnergy ν z i + μ * planeSq (bodyVector z.2 i) / 2 := by
  unfold reducedKeplerEnergy keplerEnergy
  field_simp
  ring

/-- **The reduced action in closed form:** for a negative heliocentric energy,
`Λ^red_i = Λ_i √(E_i / E^red_i) / s_i`, `s_i = √(1 + μ ν_i)`. With `E^red_i = E_i + μ|p_i|²/2`
(`reducedKeplerEnergy_eq_add`) this is the exact form of the oscillation `G_i - Λ_i` of the scoping
note's consistency check, `μ ν_i Λ_i (a_i/|q_i| - 1) + O(μ²)` to first order. -/
theorem keplerAction_redMass_eq_mul (hν : 0 < ν i) (hs : 0 < 1 + μ * ν i) (z : Phase (n * 2))
    (hE : keplerEnergy ν z i < 0) :
    keplerAction (redMass ν μ) z i = keplerAction ν z i *
      Real.sqrt (keplerEnergy ν z i / reducedKeplerEnergy ν μ z i) / Real.sqrt (1 + μ * ν i) := by
  have ha : 0 ≤ keplerAxis ν z i := by
    unfold keplerAxis
    exact div_nonneg_of_nonpos (by linarith) (by linarith)
  have hax : keplerAxis (redMass ν μ) z i =
      keplerAxis ν z i * (keplerEnergy ν z i / reducedKeplerEnergy ν μ z i) := by
    rw [keplerAxis_redMass hν hs, reducedKeplerAxis_eq hs]
    unfold keplerAxis
    rw [div_mul_div_comm, mul_comm (2 : ℝ) (keplerEnergy ν z i), mul_assoc,
      mul_comm (-ν i) (keplerEnergy ν z i), mul_div_mul_left _ _ hE.ne]
  unfold keplerAction
  rw [hax, Real.sqrt_mul ha]
  unfold redMass
  ring

end Identity

end KAM.Application.LambdaDrift

end
