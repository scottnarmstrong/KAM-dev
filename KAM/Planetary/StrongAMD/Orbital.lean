/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Frozen.Planetary.Defs.KeplerEnergy
public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerEccVector

/-!
# Elementary orbital identities, planar, without a prograde premise

Source: `LP:MAIN L2 (110–128)`, definitions `LP:MAIN §1 (26–45)`; track LP, non-frozen.

For one planet with `0 < ν i`, `0 < |q_i|` and negative Kepler energy (and **no** sign condition
on the angular momentum `L_i = q_i × p_i`, so the radial case `e_i = 1`, `L_i = 0` is included):
`orbital_identities` bundles `0 < a`, `0 < Λ`, `Λ² = ν² a`, (11) `e² = 1 - L²/Λ²`, `e ≤ 1`,
`|L| = Λ √(1 - e²)`, `|L| ≤ Λ`, and (12) `a (1 - e) ≤ |q| ≤ a (1 + e)`, `|p|² = ν² (2/|q| - 1/a)`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Kepler KAM.Planetary

variable {n : ℕ}

/-- Lagrange's identity for the eccentricity vector (distinct from the private
`KAM.Planetary.planeSq_ecc_aux`). -/
theorem planeSq_eccVector_identity {m : ℝ} {q p : Fin 2 → ℝ} (hm : 0 < m) (hr : 0 < planeLength q) :
    planeSq ((planeSq p / m ^ 2 - 1 / planeLength q) • q - (planeDot q p / m ^ 2) • p) =
      1 + 2 * (planeSq p / (2 * m) - m / planeLength q) * planeCross q p ^ 2 / m ^ 3 := by
  have hq : planeLength q ^ 2 = planeSq q := KAM.Kepler.planeLength_sq q
  have hq' : planeSq q = q 0 ^ 2 + q 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
  have hp' : planeSq p = p 0 ^ 2 + p 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
  have hd : planeDot q p = q 0 * p 0 + q 1 * p 1 := by simp [planeDot, Fin.sum_univ_two]
  have hc : planeCross q p = q 0 * p 1 - q 1 * p 0 := rfl
  have hne : planeLength q ≠ 0 := hr.ne'
  set r := planeLength q
  have hq2 : r ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by rw [hq, hq']
  have hexp : planeSq ((planeSq p / m ^ 2 - 1 / r) • q - (planeDot q p / m ^ 2) • p) =
      ((planeSq p / m ^ 2 - 1 / r) * q 0 - planeDot q p / m ^ 2 * p 0) ^ 2 +
        ((planeSq p / m ^ 2 - 1 / r) * q 1 - planeDot q p / m ^ 2 * p 1) ^ 2 := by
    simp [planeSq, Fin.sum_univ_two]
  rw [hexp, hp', hd, hc]
  field_simp
  linear_combination (-m ^ 4) * hq2

/-- The radial component `q · e = L²/ν² - |q|` of the eccentricity vector (any sign of `L`). -/
theorem planeDot_eccVector {m : ℝ} {q p : Fin 2 → ℝ} (hm : 0 < m) (hr : 0 < planeLength q) :
    planeDot q ((planeSq p / m ^ 2 - 1 / planeLength q) • q - (planeDot q p / m ^ 2) • p) =
      planeCross q p ^ 2 / m ^ 2 - planeLength q := by
  have hq : planeLength q ^ 2 = planeSq q := KAM.Kepler.planeLength_sq q
  have hq' : planeSq q = q 0 ^ 2 + q 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
  have hp' : planeSq p = p 0 ^ 2 + p 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
  have hd : planeDot q p = q 0 * p 0 + q 1 * p 1 := by simp [planeDot, Fin.sum_univ_two]
  have hd2 : ∀ w : Fin 2 → ℝ, planeDot q w = q 0 * w 0 + q 1 * w 1 := by
    intro w; simp [planeDot, Fin.sum_univ_two]
  have hc : planeCross q p = q 0 * p 1 - q 1 * p 0 := rfl
  have hne : planeLength q ≠ 0 := hr.ne'
  set r := planeLength q
  have hq2 : r ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by rw [hq, hq']
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd2]
  rw [hc, hp']
  field_simp
  linear_combination (m ^ 2) * hq2

/-- Pure real-variable core of `orbital_identities`: `μ` mass, `r` radius, `s = |p|²`, `C = L`
the angular momentum (any sign), `E` energy, `a` axis, `Λ` action, `S = |e|²`, `D = q·e`,
`ε = |e|`. -/
theorem orbital_scalar {μ r s C E a Λ S D ε : ℝ} (hm : 0 < μ) (hr : 0 < r) (hs : 0 ≤ s)
    (hE : E < 0) (hEdef : E = s / (2 * μ) - μ / r) (haxis : a = -μ / (2 * E))
    (hact : Λ = μ * Real.sqrt a) (hecc2 : S = 1 + 2 * E * C ^ 2 / μ ^ 3) (hesq : ε ^ 2 = S)
    (hdot2 : D = C ^ 2 / μ ^ 2 - r) (hnn : 0 ≤ ε) (hD : |D| ≤ r * ε) :
    0 < a ∧ 0 < Λ ∧ Λ ^ 2 = μ ^ 2 * a ∧ ε ^ 2 = 1 - C ^ 2 / Λ ^ 2 ∧ ε ≤ 1 ∧
    |C| = Λ * Real.sqrt (1 - ε ^ 2) ∧ |C| ≤ Λ ∧
    a * (1 - ε) ≤ r ∧ r ≤ a * (1 + ε) ∧ s = μ ^ 2 * (2 / r - 1 / a) := by
  have hE2 : 2 * E < 0 := by linarith
  have ha : 0 < a := by rw [haxis]; exact div_pos_of_neg_of_neg (by linarith) hE2
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hΛ : 0 < Λ := by rw [hact]; exact mul_pos hm hsq
  have hΛ2 : Λ ^ 2 = μ ^ 2 * a := by rw [hact, mul_pow, Real.sq_sqrt ha.le]
  have haE : a * (2 * E) = -μ := by
    have := hE.ne
    rw [haxis]; field_simp
  have hEΛ : E = -μ ^ 3 / (2 * Λ ^ 2) := by
    rw [hΛ2, eq_div_iff (by positivity)]
    linear_combination (μ ^ 2) * haE
  have hec2 : ε ^ 2 = 1 - C ^ 2 / Λ ^ 2 := by
    rw [hesq, hecc2, hEΛ]
    have := hΛ.ne'
    have := hm.ne'
    field_simp
    ring
  have hCΛ2 : 0 ≤ C ^ 2 / Λ ^ 2 := by positivity
  have hε1 : ε ≤ 1 := by nlinarith
  have hCΛ : |C| = Λ * Real.sqrt (1 - ε ^ 2) := by
    rw [hec2]
    have h1 : 1 - (1 - C ^ 2 / Λ ^ 2) = (C / Λ) ^ 2 := by ring
    rw [h1, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hΛ]
    field_simp
  have hsqe : Real.sqrt (1 - ε ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have hCle : |C| ≤ Λ := by
    rw [hCΛ]; nlinarith [Real.sqrt_nonneg (1 - ε ^ 2)]
  have hdot1 : D = a * (1 - ε ^ 2) - r := by
    rw [hdot2, hec2]
    have h1 : a * (1 - (1 - C ^ 2 / Λ ^ 2)) = C ^ 2 / μ ^ 2 := by
      have := hm.ne'
      have := ha.ne'
      have := hΛ.ne'
      rw [hΛ2]
      field_simp
      ring
    rw [h1]
  have hsform : s = μ ^ 2 * (2 / r - 1 / a) := by
    have h1 : s = 2 * μ * (E + μ / r) := by rw [hEdef]; field_simp; ring
    have h2 : 1 / a = -2 * E / μ := by rw [haxis]; field_simp
    rw [h2, h1]
    have := hr.ne'
    have := hm.ne'
    field_simp
    ring
  rw [abs_le] at hD
  obtain ⟨hl, hu⟩ := hD
  have h1e' : 0 < 1 + ε := by linarith
  have hmul : a * (1 - ε ^ 2) = (1 + ε) * (a * (1 - ε)) := by ring
  have hlow : a * (1 - ε) ≤ r := by
    rw [hdot1] at hu
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_left h h1e'
    nlinarith
  have hup : r ≤ a * (1 + ε) := by
    rcases lt_or_eq_of_le hε1 with hlt | heq
    · have h1e : 0 < 1 - ε := by linarith
      rw [hdot1] at hl
      by_contra h
      push Not at h
      have := mul_lt_mul_of_pos_left h h1e
      nlinarith
    · -- radial case `ε = 1`: `r ≤ 2a` from `0 ≤ |p|²`
      rw [heq]
      have hs' : 0 ≤ μ ^ 2 * (2 / r - 1 / a) := hsform ▸ hs
      have hpos : 0 ≤ 2 / r - 1 / a := nonneg_of_mul_nonneg_right hs' (by positivity)
      have h3 : 1 / a ≤ 2 / r := by linarith
      rw [div_le_div_iff₀ ha hr] at h3
      linarith
  exact ⟨ha, hΛ, hΛ2, hec2, hε1, hCΛ, hCle, hlow, hup, hsform⟩

/-- **Lemma 2, planar, no prograde premise** (`LP:MAIN L2 (110–128)`): the elementary orbital
identities (11) and (12) for planet `i`, premises `0 < ν i`, `0 < |q_i|`, `E_i < 0`. -/
theorem orbital_identities {ν : Fin n → ℝ} {z : Phase (n * 2)} (i : Fin n)
    (hz : 0 < ν i ∧ 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0) :
    0 < keplerAxis ν z i ∧ 0 < keplerAction ν z i ∧
    keplerAction ν z i ^ 2 = ν i ^ 2 * keplerAxis ν z i ∧
    planeLength (keplerEccVector ν z i) ^ 2 =
      1 - planeCross (bodyVector z.1 i) (bodyVector z.2 i) ^ 2 / keplerAction ν z i ^ 2 ∧
    planeLength (keplerEccVector ν z i) ≤ 1 ∧
    |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| =
      keplerAction ν z i * Real.sqrt (1 - planeLength (keplerEccVector ν z i) ^ 2) ∧
    |planeCross (bodyVector z.1 i) (bodyVector z.2 i)| ≤ keplerAction ν z i ∧
    keplerAxis ν z i * (1 - planeLength (keplerEccVector ν z i)) ≤
      planeLength (bodyVector z.1 i) ∧
    planeLength (bodyVector z.1 i) ≤
      keplerAxis ν z i * (1 + planeLength (keplerEccVector ν z i)) ∧
    planeSq (bodyVector z.2 i) =
      ν i ^ 2 * (2 / planeLength (bodyVector z.1 i) - 1 / keplerAxis ν z i) := by
  obtain ⟨hm, hr, hE⟩ := hz
  have hEdef : keplerEnergy ν z i =
      planeSq (bodyVector z.2 i) / (2 * ν i) - ν i / planeLength (bodyVector z.1 i) := rfl
  have haxis : keplerAxis ν z i = -ν i / (2 * keplerEnergy ν z i) := rfl
  have hactdef : keplerAction ν z i = ν i * Real.sqrt (keplerAxis ν z i) := rfl
  have heccdef : keplerEccVector ν z i =
      (planeSq (bodyVector z.2 i) / ν i ^ 2 - 1 / planeLength (bodyVector z.1 i)) •
        bodyVector z.1 i -
      (planeDot (bodyVector z.1 i) (bodyVector z.2 i) / ν i ^ 2) • bodyVector z.2 i := rfl
  have hecc2 := planeSq_eccVector_identity (m := ν i) (q := bodyVector z.1 i)
    (p := bodyVector z.2 i) hm hr
  rw [← heccdef, ← hEdef] at hecc2
  have hesq := KAM.Kepler.planeLength_sq (keplerEccVector ν z i)
  have hdot2 : planeDot (bodyVector z.1 i) (keplerEccVector ν z i) =
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) ^ 2 / ν i ^ 2 -
        planeLength (bodyVector z.1 i) := by
    rw [heccdef]
    exact planeDot_eccVector hm hr
  have hnn := KAM.Kepler.planeLength_nonneg (keplerEccVector ν z i)
  have hD := KAM.Kepler.abs_planeDot_le (bodyVector z.1 i) (keplerEccVector ν z i)
  have hs : 0 ≤ planeSq (bodyVector z.2 i) := by
    rw [← KAM.Kepler.planeLength_sq]; positivity
  clear heccdef
  generalize planeSq (keplerEccVector ν z i) = S at *
  generalize planeDot (bodyVector z.1 i) (keplerEccVector ν z i) = D at *
  generalize planeLength (keplerEccVector ν z i) = ε at *
  generalize planeSq (bodyVector z.2 i) = s at *
  generalize planeCross (bodyVector z.1 i) (bodyVector z.2 i) = C at *
  generalize planeLength (bodyVector z.1 i) = r at *
  generalize keplerEnergy ν z i = E at *
  generalize keplerAxis ν z i = a at *
  generalize keplerAction ν z i = Λ at *
  generalize ν i = μ at *
  exact orbital_scalar hm hr hs hE hEdef haxis hactdef hecc2 hesq hdot2 hnn hD

end KAM.Planetary.StrongAMD

end
