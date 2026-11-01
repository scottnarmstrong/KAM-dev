/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Elements
public import KAM.Planetary.StrongAMD.Orbital

/-!
# Elementary orbital identities in dimension three (no prograde premise)

Package LP-SP-MODEL, `LP:MAIN L2 (110–128)`, `d = 3`; track LP, non-frozen; the statement surface
is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For one planet with `0 < ν i`, `0 < |q_i|`, negative energy (the radial case `e = 1`, `L_i = 0` is
included): `spatial_orbital_identities` bundles `0 < a`, `0 < Λ`, `Λ² = ν² a`, (11)
`e² = 1 − |L_i|²/Λ²`, `e ≤ 1`, `|L_i| = Λ √(1 − e²)`, `|L_i| ≤ Λ`, and (12)
`a (1 − e) ≤ |q| ≤ a (1 + e)`, `|p|² = ν² (2/|q| − 1/a)`.  The proof reduces to the dimension-free
scalar core `KAM.Planetary.StrongAMD.orbital_scalar`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n : ℕ}

theorem spaceSq_smul_sub_smul (a b : ℝ) (q p : Fin 3 → ℝ) :
    spaceSq (a • q - b • p) =
      a ^ 2 * spaceSq q - 2 * a * b * spaceDot q p + b ^ 2 * spaceSq p := by
  simp only [spaceSq_def, spaceDot_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem spaceDot_smul_sub_smul (a b : ℝ) (q p : Fin 3 → ℝ) :
    spaceDot q (a • q - b • p) = a * spaceSq q - b * spaceDot q p := by
  simp only [spaceSq_def, spaceDot_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- Lagrange's identity for the eccentricity vector. -/
theorem spaceSq_eccVector_identity {m : ℝ} {q p : Fin 3 → ℝ} (hm : 0 < m)
    (hr : 0 < spaceLength q) :
    spaceSq ((spaceSq p / m ^ 2 - 1 / spaceLength q) • q - (spaceDot q p / m ^ 2) • p) =
      1 + 2 * (spaceSq p / (2 * m) - m / spaceLength q) * spaceSq (spaceCross q p) / m ^ 3 := by
  have hq : spaceLength q ^ 2 = spaceSq q := spaceLength_sq q
  have hl := spaceSq_mul_spaceSq q p
  have hne : spaceLength q ≠ 0 := hr.ne'
  rw [spaceSq_smul_sub_smul]
  have hX : spaceSq (spaceCross q p) = spaceSq q * spaceSq p - spaceDot q p ^ 2 := by
    linarith
  rw [hX, ← hq]
  field_simp
  ring

/-- The radial component `q · 𝐞 = |L|²/ν² − |q|` of the eccentricity vector. -/
theorem spaceDot_eccVector {m : ℝ} {q p : Fin 3 → ℝ} (hm : 0 < m) (hr : 0 < spaceLength q) :
    spaceDot q ((spaceSq p / m ^ 2 - 1 / spaceLength q) • q - (spaceDot q p / m ^ 2) • p) =
      spaceSq (spaceCross q p) / m ^ 2 - spaceLength q := by
  have hq : spaceLength q ^ 2 = spaceSq q := spaceLength_sq q
  have hl := spaceSq_mul_spaceSq q p
  have hne : spaceLength q ≠ 0 := hr.ne'
  rw [spaceDot_smul_sub_smul]
  have hX : spaceSq (spaceCross q p) = spaceSq q * spaceSq p - spaceDot q p ^ 2 := by
    linarith
  rw [hX, ← hq]
  field_simp
  ring

/-- **Lemma 2, `d = 3`, no prograde premise** (`LP:MAIN L2 (110–128)`): the elementary orbital
identities (11) and (12) for planet `i`; premises `0 < ν i`, `0 < |q_i|`, `E_i < 0`. -/
theorem spatial_orbital_identities {ν : Fin n → ℝ} {z : Phase (n * 3)} (i : Fin n)
    (hz : 0 < ν i ∧ 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialKeplerEnergy ν z i < 0) :
    0 < spatialKeplerAxis ν z i ∧ 0 < spatialKeplerAction ν z i ∧
    spatialKeplerAction ν z i ^ 2 = ν i ^ 2 * spatialKeplerAxis ν z i ∧
    spaceLength (spatialKeplerEccVector ν z i) ^ 2 =
      1 - spaceLength (planetAngularMomentum3 z i) ^ 2 / spatialKeplerAction ν z i ^ 2 ∧
    spaceLength (spatialKeplerEccVector ν z i) ≤ 1 ∧
    spaceLength (planetAngularMomentum3 z i) =
      spatialKeplerAction ν z i *
        Real.sqrt (1 - spaceLength (spatialKeplerEccVector ν z i) ^ 2) ∧
    spaceLength (planetAngularMomentum3 z i) ≤ spatialKeplerAction ν z i ∧
    spatialKeplerAxis ν z i * (1 - spaceLength (spatialKeplerEccVector ν z i)) ≤
      spaceLength (bodyVector3 z.1 i) ∧
    spaceLength (bodyVector3 z.1 i) ≤
      spatialKeplerAxis ν z i * (1 + spaceLength (spatialKeplerEccVector ν z i)) ∧
    spaceSq (bodyVector3 z.2 i) =
      ν i ^ 2 * (2 / spaceLength (bodyVector3 z.1 i) - 1 / spatialKeplerAxis ν z i) := by
  obtain ⟨hm, hr, hE⟩ := hz
  have hEdef : spatialKeplerEnergy ν z i =
      spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i) := rfl
  have haxis : spatialKeplerAxis ν z i = -ν i / (2 * spatialKeplerEnergy ν z i) := rfl
  have hactdef : spatialKeplerAction ν z i = ν i * Real.sqrt (spatialKeplerAxis ν z i) := rfl
  have heccdef : spatialKeplerEccVector ν z i =
      (spaceSq (bodyVector3 z.2 i) / ν i ^ 2 - 1 / spaceLength (bodyVector3 z.1 i)) •
        bodyVector3 z.1 i -
      (spaceDot (bodyVector3 z.1 i) (bodyVector3 z.2 i) / ν i ^ 2) • bodyVector3 z.2 i := rfl
  have hLdef : planetAngularMomentum3 z i =
      spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i) := rfl
  have hecc2 := spaceSq_eccVector_identity (m := ν i) (q := bodyVector3 z.1 i)
    (p := bodyVector3 z.2 i) hm hr
  rw [← heccdef, ← hEdef] at hecc2
  have hesq := spaceLength_sq (spatialKeplerEccVector ν z i)
  have hdot2 : spaceDot (bodyVector3 z.1 i) (spatialKeplerEccVector ν z i) =
      spaceLength (planetAngularMomentum3 z i) ^ 2 / ν i ^ 2 -
        spaceLength (bodyVector3 z.1 i) := by
    rw [heccdef, spaceDot_eccVector hm hr, spaceLength_sq, hLdef]
  have hecc2' : spaceSq (spatialKeplerEccVector ν z i) = 1 + 2 * spatialKeplerEnergy ν z i *
      spaceLength (planetAngularMomentum3 z i) ^ 2 / ν i ^ 3 := by
    rw [hecc2, spaceLength_sq, hLdef]
  have hnn := spaceLength_nonneg (spatialKeplerEccVector ν z i)
  have hD := abs_spaceDot_le (bodyVector3 z.1 i) (spatialKeplerEccVector ν z i)
  have hs : 0 ≤ spaceSq (bodyVector3 z.2 i) := spaceSq_nonneg _
  have hC0 := spaceLength_nonneg (planetAngularMomentum3 z i)
  have key := KAM.Planetary.StrongAMD.orbital_scalar (C := spaceLength (planetAngularMomentum3 z i))
    hm hr hs hE hEdef haxis hactdef hecc2' hesq hdot2 hnn hD
  rw [abs_of_nonneg hC0] at key
  exact key

end KAM.Planetary.Spatial

end
