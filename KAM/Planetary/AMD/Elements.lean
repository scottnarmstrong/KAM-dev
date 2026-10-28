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
public import KAM.Frozen.Planetary.Defs.ProgradeElliptic
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Frozen.Planetary.Defs.TotalMomentum

/-!
# Elementary Kepler elements and the eccentricity bound (P14, package A1)

Blueprint P, Part 14 (`bpP:p14:elements`, `bpP:p14:ecc-bound`).  For one planet with positive
mass, positive radius, negative Kepler energy and positive angular momentum, `elements` exports
the elementary clauses (a)–(f) relating axis, action, angular momentum and the eccentricity
vector; `eccentricity_deficit` is the threshold deficit estimate; `ecc_bound` turns a bound on the
physical AMD into a uniform eccentricity bound.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

variable {n : ℕ}

/-- Scalar identity behind `|e|² = 1 - C²/Λ²`: Lagrange's identity for the eccentricity vector. -/
private theorem planeSq_ecc_aux {m : ℝ} {q p : Fin 2 → ℝ} (hm : 0 < m) (hr : 0 < planeLength q) :
    planeSq ((planeSq p / m ^ 2 - 1 / planeLength q) • q - (planeDot q p / m ^ 2) • p) =
      1 + 2 * (planeSq p / (2 * m) - m / planeLength q) * planeCross q p ^ 2 / m ^ 3 := by
  have hq : planeLength q ^ 2 = planeSq q := KAM.Kepler.planeLength_sq q
  have hL := KAM.Kepler.planeSq_mul_planeSq q p
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

/-- Pure real-variable core of `elements`: `μ` mass, `r` radius, `s = |p|²`, `C` angular momentum,
`E` energy, `a` axis, `Λ` action, `S = |e|²`, `D = q·e`, `ε = |e|`. -/
private theorem elements_scalar {μ r s C E a Λ S D ε : ℝ} (hm : 0 < μ) (hr : 0 < r) (hE : E < 0)
    (hC : 0 < C) (hEdef : E = s / (2 * μ) - μ / r) (haxis : a = -μ / (2 * E))
    (hact : Λ = μ * Real.sqrt a) (hecc2 : S = 1 + 2 * E * C ^ 2 / μ ^ 3) (hesq : ε ^ 2 = S)
    (hdot2 : D = C ^ 2 / μ ^ 2 - r) (hnn : 0 ≤ ε) (hD : |D| ≤ r * ε) :
    0 < a ∧ 0 < Λ ∧ Λ ^ 2 = μ ^ 2 * a ∧ E = -μ ^ 3 / (2 * Λ ^ 2) ∧
    ε ^ 2 = 1 - C ^ 2 / Λ ^ 2 ∧ ε < 1 ∧ C = Λ * Real.sqrt (1 - ε ^ 2) ∧
    D = a * (1 - ε ^ 2) - r ∧ a * (1 - ε) ≤ r ∧ r ≤ a * (1 + ε) ∧ s < 2 * μ ^ 2 / r ∧
    (0 < C ∧ C ≤ Λ) ∧ 0 ≤ ε ∧ D = C ^ 2 / μ ^ 2 - r ∧
    Λ - C = Λ * (1 - Real.sqrt (1 - ε ^ 2)) ∧ 0 ≤ Λ - C := by
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
  have hCΛ2 : 0 < C ^ 2 / Λ ^ 2 := by positivity
  have hpos : 0 < 1 - ε ^ 2 := by rw [hec2]; linarith
  have hlt : ε < 1 := by nlinarith
  have hCΛ : C = Λ * Real.sqrt (1 - ε ^ 2) := by
    rw [hec2]
    have h1 : 1 - (1 - C ^ 2 / Λ ^ 2) = (C / Λ) ^ 2 := by ring
    rw [h1, Real.sqrt_sq (by positivity)]
    field_simp
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
  rw [abs_le] at hD
  obtain ⟨hl, hu⟩ := hD
  have h1e : 0 < 1 - ε := by linarith
  have h1e' : 0 < 1 + ε := by linarith
  have hsqe : Real.sqrt (1 - ε ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have hsqe0 : 0 ≤ Real.sqrt (1 - ε ^ 2) := Real.sqrt_nonneg _
  have hmul : a * (1 - ε ^ 2) = (1 + ε) * (a * (1 - ε)) := by ring
  have hmul' : a * (1 - ε ^ 2) = (1 - ε) * (a * (1 + ε)) := by ring
  refine ⟨ha, hΛ, hΛ2, hEΛ, hec2, hlt, hCΛ, hdot1, ?_, ?_, ?_, ⟨hC, ?_⟩, hnn, hdot2, ?_, ?_⟩
  · rw [hdot1] at hu
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_left h h1e'
    nlinarith
  · rw [hdot1] at hl
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_left h h1e
    nlinarith
  · have hs : s / (2 * μ) < μ / r := by linarith
    rw [lt_div_iff₀ hr]
    rw [div_lt_iff₀ (by positivity)] at hs
    have h2 : s * r < μ / r * (2 * μ) * r := mul_lt_mul_of_pos_right hs hr
    have h3 : μ / r * (2 * μ) * r = 2 * μ ^ 2 := by field_simp
    linarith
  · rw [hCΛ]; nlinarith
  · rw [hCΛ]; ring
  · rw [hCΛ]; nlinarith

/-- Clauses (a)–(f) for one planet: axis, action, energy, eccentricity vector, radial bounds. -/
theorem elements {m : Fin n → ℝ} {z : Phase (n * 2)} (i : Fin n)
    (hz : 0 < m i ∧ 0 < planeLength (bodyVector z.1 i) ∧
      keplerEnergy m z i < 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)) :
    0 < keplerAxis m z i ∧ 0 < keplerAction m z i ∧
    keplerAction m z i ^ 2 = m i ^ 2 * keplerAxis m z i ∧
    keplerEnergy m z i = -(m i)^3 / (2 * keplerAction m z i ^ 2) ∧
    planeLength (keplerEccVector m z i)^2 = 1 -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)^2 / keplerAction m z i ^ 2 ∧
    planeLength (keplerEccVector m z i) < 1 ∧
    planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
      keplerAction m z i * Real.sqrt (1 - planeLength (keplerEccVector m z i)^2) ∧
    planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      keplerAxis m z i * (1 - planeLength (keplerEccVector m z i)^2) -
        planeLength (bodyVector z.1 i) ∧
    keplerAxis m z i * (1 - planeLength (keplerEccVector m z i)) ≤
      planeLength (bodyVector z.1 i) ∧
    planeLength (bodyVector z.1 i) ≤
      keplerAxis m z i * (1 + planeLength (keplerEccVector m z i)) ∧
    planeSq (bodyVector z.2 i) < 2 * m i ^ 2 / planeLength (bodyVector z.1 i) ∧
    (0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i) ∧
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) ≤ keplerAction m z i) ∧
    0 ≤ planeLength (keplerEccVector m z i) ∧
    planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)^2 / m i^2 -
        planeLength (bodyVector z.1 i) ∧
    keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
      keplerAction m z i * (1 - Real.sqrt (1 - planeLength (keplerEccVector m z i)^2)) ∧
    0 ≤ keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  obtain ⟨hm, hr, hE, hC⟩ := hz
  have hEdef : keplerEnergy m z i =
      planeSq (bodyVector z.2 i) / (2 * m i) - m i / planeLength (bodyVector z.1 i) := rfl
  have haxis : keplerAxis m z i = -m i / (2 * keplerEnergy m z i) := rfl
  have hactdef : keplerAction m z i = m i * Real.sqrt (keplerAxis m z i) := rfl
  have heccdef : keplerEccVector m z i =
      (planeSq (bodyVector z.2 i) / m i ^ 2 - 1 / planeLength (bodyVector z.1 i)) •
        bodyVector z.1 i -
      (planeDot (bodyVector z.1 i) (bodyVector z.2 i) / m i ^ 2) • bodyVector z.2 i := rfl
  have hLag := KAM.Kepler.planeSq_mul_planeSq (bodyVector z.1 i) (bodyVector z.2 i)
  have hrsq := KAM.Kepler.planeLength_sq (bodyVector z.1 i)
  have hecc2 := planeSq_ecc_aux (m := m i) (q := bodyVector z.1 i) (p := bodyVector z.2 i) hm hr
  rw [← heccdef, ← hEdef] at hecc2
  have hesq := KAM.Kepler.planeLength_sq (keplerEccVector m z i)
  have hdot2 : planeDot (bodyVector z.1 i) (keplerEccVector m z i) =
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) ^ 2 / m i ^ 2 -
        planeLength (bodyVector z.1 i) := by
    rw [heccdef]
    have hq' : planeSq (bodyVector z.1 i) =
        bodyVector z.1 i 0 ^ 2 + bodyVector z.1 i 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
    have hp' : planeSq (bodyVector z.2 i) =
        bodyVector z.2 i 0 ^ 2 + bodyVector z.2 i 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
    have hd : planeDot (bodyVector z.1 i) (bodyVector z.2 i) =
        bodyVector z.1 i 0 * bodyVector z.2 i 0 + bodyVector z.1 i 1 * bodyVector z.2 i 1 := by
      simp [planeDot, Fin.sum_univ_two]
    have hd2 : ∀ w : Fin 2 → ℝ, planeDot (bodyVector z.1 i) w =
        bodyVector z.1 i 0 * w 0 + bodyVector z.1 i 1 * w 1 := by
      intro w; simp [planeDot, Fin.sum_univ_two]
    have hc : planeCross (bodyVector z.1 i) (bodyVector z.2 i) =
        bodyVector z.1 i 0 * bodyVector z.2 i 1 - bodyVector z.1 i 1 * bodyVector z.2 i 0 := rfl
    have hr0 := hr.ne'
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd2]
    rw [hc, hp']
    have hq2 : planeLength (bodyVector z.1 i) ^ 2 =
        bodyVector z.1 i 0 ^ 2 + bodyVector z.1 i 1 ^ 2 := by rw [hrsq, hq']
    field_simp
    linear_combination (m i ^ 2) * hq2
  have hnn := KAM.Kepler.planeLength_nonneg (keplerEccVector m z i)
  have hD := KAM.Kepler.abs_planeDot_le (bodyVector z.1 i) (keplerEccVector m z i)
  clear heccdef hLag hrsq
  generalize planeSq (keplerEccVector m z i) = S at *
  generalize planeDot (bodyVector z.1 i) (keplerEccVector m z i) = D at *
  generalize planeLength (keplerEccVector m z i) = ε at *
  generalize planeSq (bodyVector z.2 i) = s at *
  generalize planeCross (bodyVector z.1 i) (bodyVector z.2 i) = C at *
  generalize planeLength (bodyVector z.1 i) = r at *
  generalize keplerEnergy m z i = E at *
  generalize keplerAxis m z i = a at *
  generalize keplerAction m z i = Λ at *
  generalize m i = μ at *
  exact elements_scalar hm hr hE hC hEdef haxis hactdef hecc2 hesq hdot2 hnn hD

/-- Threshold deficit: the angular-momentum deficit of planet `i` dominates the deficit at any
smaller eccentricity `e`. -/
theorem eccentricity_deficit {m : Fin n → ℝ} {z : Phase (n * 2)}
    (i : Fin n)
    (hz : 0 < m i ∧ 0 < planeLength (bodyVector z.1 i) ∧
      keplerEnergy m z i < 0 ∧
      0 < planeCross (bodyVector z.1 i) (bodyVector z.2 i)) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hle : e ≤ planeLength (keplerEccVector m z i)) :
    keplerAction m z i * (1 - Real.sqrt (1 - e ^ 2)) ≤
      keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  have _ := he1
  obtain ⟨-, hΛ, -, -, -, -, -, -, -, -, -, -, -, -, hdef, -⟩ := elements i hz
  rw [hdef]
  have h1 : e ^ 2 ≤ planeLength (keplerEccVector m z i) ^ 2 := pow_le_pow_left₀ he hle 2
  have h2 : Real.sqrt (1 - planeLength (keplerEccVector m z i) ^ 2) ≤
      Real.sqrt (1 - e ^ 2) := Real.sqrt_le_sqrt (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) hΛ.le

/-- AMD below the single-planet threshold forces every eccentricity below `e`. -/
theorem ecc_bound {m lo : Fin n → ℝ} {z : Phase (n * 2)} {A e : ℝ}
    (hz : ProgradeElliptic m z) (hlo : ∀ i, 0 < lo i)
    (hact : ∀ i, lo i < keplerAction m z i) (hA : physicalAMD m z < A)
    (he : 0 < e) (he1 : e < 1)
    (hbar : ∀ i, A ≤ lo i * (1 - Real.sqrt (1 - e ^ 2))) :
    ∀ i, planeLength (keplerEccVector m z i) < e ∧
      keplerAction m z i * Real.sqrt (1 - e ^ 2) <
        planeCross (bodyVector z.1 i) (bodyVector z.2 i) := by
  have hdef : ∀ i, 0 ≤ keplerAction m z i -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i) := fun i => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := elements i (hz i)
    exact h
  have hsum : physicalAMD m z = ∑ i, (keplerAction m z i -
      planeCross (bodyVector z.1 i) (bodyVector z.2 i)) := by
    unfold physicalAMD totalMomentum
    rw [Finset.sum_sub_distrib]
  have hle : ∀ i, keplerAction m z i - planeCross (bodyVector z.1 i) (bodyVector z.2 i) <
      A := fun i =>
    lt_of_le_of_lt (hsum ▸ Finset.single_le_sum (fun j _ => hdef j) (Finset.mem_univ i)) hA
  have hs0 : 0 < 1 - Real.sqrt (1 - e ^ 2) := by
    have : Real.sqrt (1 - e ^ 2) < 1 := by
      rw [Real.sqrt_lt' one_pos]; nlinarith
    linarith
  have hsle : Real.sqrt (1 - e ^ 2) ≤ 1 := by linarith
  intro i
  have hΛ := hact i
  have hl := hlo i
  have hd := hle i
  have hb := hbar i
  have hmul : lo i * (1 - Real.sqrt (1 - e ^ 2)) <
      keplerAction m z i * (1 - Real.sqrt (1 - e ^ 2)) :=
    mul_lt_mul_of_pos_right hΛ hs0
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have := eccentricity_deficit i (hz i) he.le he1 h
    linarith
  · nlinarith

end KAM.Planetary

end
