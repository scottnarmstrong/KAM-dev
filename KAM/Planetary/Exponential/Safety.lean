/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Frozen.Planetary.Defs.PlanetaryDriftExponent
public import KAM.Frozen.Planetary.Defs.PlanetaryTimeExponent
public import KAM.Frozen.Planetary.Defs.StoppedActionBound
public import KAM.Planetary.AMD.Confinement

/-!
# P14 package E12: exponential safety from the stopped action bound

Blueprint P, Part 14 (`bpP:p14:expsafe`, steps `es-const`, `es-par`, `es-stop`, `es-amd`,
`es-axis`, `es-assemble`).  The theorem `expsafe_of_stopped` proves the statement of `expsafe`
(the frozen type of P-EXP-SAFE) from the signed statement of `stopped` (Proposition
`bpP:p14:stopped`), taken verbatim as its only extra hypothesis `hstop`.

From the constants `B₀ ≥ 1` and `ν₀ ∈ (0, 1]` of `hstop`, the margin `θ` of the fixed box
(`amdBox_exists_margin`) gives `μ* = B₀⁻¹ min(ν₀/2, (θ/2)^{1/b})`, `c = B₀^{-a}` and
`C = B₀^b ∑ᵢ uᵢ/mᵢ²`.  For `0 < μ < μ*`, with `ν = B₀ μ`, the horizon `T = exp(c μ^{-a})` equals
`exp(ν^{-a}) ≤ ν⁻¹ exp(ν^{-a})` and `δ = ν^b/2` satisfies all collar margins of `amd`
(package A6).  The axis drift follows from `aᵢ = (Λᵢ/mᵢ)²` (`keplerAxis_eq_action_div_sq`) and
the action drift `δ` (`keplerAxis_drift_le`).

The constant `C` uses the sum `∑ᵢ uᵢ/mᵢ²` in place of the blueprint's `maxᵢ uᵢ/mᵢ²`; it is a
larger positive constant depending only on `B`, so the statement is unchanged.  The blueprint's
margin `θ` also contains `κ` and `ε_D`; they are internal to the proof of `stopped` and are not
needed once `stopped` is a hypothesis.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {n : ℕ}

/-- The exponent `a = αₙ` of P-EXP-SAFE is positive. -/
theorem planetaryTimeExponent_pos (n : ℕ) : 0 < planetaryTimeExponent n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 6 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 14 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  exact div_pos two_pos hden

/-- The exponent `b = βₙ = 3αₙ/2` of P-EXP-SAFE is positive. -/
theorem planetaryDriftExponent_pos (n : ℕ) : 0 < planetaryDriftExponent n := by
  have := planetaryTimeExponent_pos n
  unfold planetaryDriftExponent
  positivity

/-- `stepP:p14:es-const`: a single positive margin below every inner action gap and below
`(A₁ - A₀)/n`. -/
theorem amdBox_exists_margin (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible) :
    ∃ θ : ℝ, 0 < θ ∧
      (∀ i, θ ≤ B.innerLower i - B.lower i ∧ θ ≤ B.upper i - B.innerUpper i) ∧
      (n : ℝ) * θ ≤ B.outerAMD - B.initialAMD := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_min
    (fun i => min (B.innerLower i - B.lower i) (B.upper i - B.innerUpper i))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hj' := hB.1 j
  have hA := hB.2.2.2.2.1
  refine ⟨min (min (B.innerLower j - B.lower j) (B.upper j - B.innerUpper j))
    ((B.outerAMD - B.initialAMD) / n), ?_, fun i => ?_, ?_⟩
  · exact lt_min (lt_min (by linarith [hj'.2.2.1]) (by linarith [hj'.2.2.2.2]))
      (div_pos (by linarith) hnpos)
  · have hi : min (min (B.innerLower j - B.lower j) (B.upper j - B.innerUpper j))
        ((B.outerAMD - B.initialAMD) / n) ≤
        min (B.innerLower i - B.lower i) (B.upper i - B.innerUpper i) :=
      (min_le_left _ _).trans (hj i)
    exact ⟨hi.trans (min_le_left _ _), hi.trans (min_le_right _ _)⟩
  · calc (n : ℝ) * min (min (B.innerLower j - B.lower j) (B.upper j - B.innerUpper j))
          ((B.outerAMD - B.initialAMD) / n)
        ≤ (n : ℝ) * ((B.outerAMD - B.initialAMD) / n) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hnpos.le
      _ = B.outerAMD - B.initialAMD := mul_div_cancel₀ _ hnpos.ne'

/-- The osculating axis is `(Λᵢ/mᵢ)²` whenever the Kepler action is positive. -/
theorem keplerAxis_eq_action_div_sq {m : Fin n → ℝ} {z : Phase (n * 2)} {i : Fin n}
    (hm : 0 < m i) (hL : 0 < keplerAction m z i) :
    keplerAxis m z i = (keplerAction m z i / m i) ^ 2 := by
  have hdef : keplerAction m z i = m i * Real.sqrt (keplerAxis m z i) := rfl
  have hs : 0 < Real.sqrt (keplerAxis m z i) := by
    rw [hdef] at hL
    exact pos_of_mul_pos_right hL hm.le
  rw [hdef, mul_div_cancel_left₀ _ hm.ne', Real.sq_sqrt (Real.sqrt_pos.1 hs).le]

/-- `stepP:p14:es-axis`: an action drift `δ` with both actions in `(0, u)` gives the axis drift
`2 (u/mᵢ²) δ`. -/
theorem keplerAxis_drift_le {m : Fin n → ℝ} {z w : Phase (n * 2)} {i : Fin n} {u δ : ℝ}
    (hm : 0 < m i) (hz : 0 < keplerAction m z i) (hzu : keplerAction m z i < u)
    (hw : 0 < keplerAction m w i) (hwu : keplerAction m w i < u)
    (hd : |keplerAction m z i - keplerAction m w i| ≤ δ) :
    |keplerAxis m z i - keplerAxis m w i| ≤ 2 * (u / m i ^ 2) * δ := by
  rw [keplerAxis_eq_action_div_sq hm hz, keplerAxis_eq_action_div_sq hm hw]
  generalize keplerAction m z i = x at *
  generalize keplerAction m w i = y at *
  have hm2 : 0 < m i ^ 2 := pow_pos hm 2
  have hxy : 0 < x + y := add_pos hz hw
  have hid : (x / m i) ^ 2 - (y / m i) ^ 2 = (x - y) * (x + y) / m i ^ 2 := by
    field_simp
    ring
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hd
  have hprod : |x - y| * (x + y) ≤ δ * (2 * u) :=
    mul_le_mul hd (by linarith) hxy.le hδ
  rw [hid, abs_div, abs_mul, abs_of_pos hxy, abs_of_pos hm2, div_le_iff₀ hm2]
  calc |x - y| * (x + y) ≤ δ * (2 * u) := hprod
    _ = 2 * (u / m i ^ 2) * δ * m i ^ 2 := by field_simp

/-- `bpP:p14:expsafe` parametric in `bpP:p14:stopped`: the exact statement of `expsafe` (the
frozen type of P-EXP-SAFE) from the signed statement of `stopped`, taken verbatim as `hstop`. -/
theorem expsafe_of_stopped {n : ℕ} (hn : 2 ≤ n)
    (hstop : ∀ (B : AMDBox n), B.Admissible →
      ∃ B0 nu0 : ℝ, 1 ≤ B0 ∧ 0 < nu0 ∧ nu0 ≤ 1 ∧
        ∀ mu T delta : ℝ, 0 < mu → B0 * mu < nu0 → 0 < T → 0 < delta →
          T ≤ (B0*mu)⁻¹ * Real.exp ((B0*mu)^(-planetaryTimeExponent n)) →
          (B0*mu)^planetaryDriftExponent n / 2 ≤ delta →
          ∀ z0 : Phase (n*2), StoppedActionBound B mu T delta z0)
    (B : AMDBox n) (hB : B.Admissible) :
    ∃ muStar c C : ℝ, 0 < muStar ∧ 0 < c ∧ 0 < C ∧
      ∀ mu : ℝ, 0 < mu → mu < muStar →
      ∀ z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD,
      ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧
        (IsMovingSolutionOn B.mass mu (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧ MovingUniqueOn B.mass mu
                    (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧
        IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-Real.exp (c * mu ^
          (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n))))
          (fun t => barycentricPositions 1 B.mass mu (z t).1)
          (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
        ∀ t ∈ (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))),
          z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
          totalMomentum (z t) = totalMomentum (z 0) ∧
          (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
            B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
            planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
          PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
        ∀ t : ℝ, |t| ≤ Real.exp (c * mu ^ (-planetaryTimeExponent n)) →
          ∀ i, |keplerAxis B.mass (z t) i - keplerAxis B.mass z0 i| ≤
            C * mu ^ planetaryDriftExponent n := by
  -- `stepP:p14:es-const`: the constants, chosen before `mu` and `z0`.
  obtain ⟨B0, nu0, hB0, hnu0, hnu01, hst⟩ := hstop B hB
  obtain ⟨θ, hθ, hθi, hθA⟩ := amdBox_exists_margin hn B hB
  have ha := planetaryTimeExponent_pos n
  have hb := planetaryDriftExponent_pos n
  have hB0pos : 0 < B0 := lt_of_lt_of_le one_pos hB0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hterm : ∀ i, 0 < B.upper i / B.mass i ^ 2 := fun i => by
    have h := hB.1 i
    exact div_pos (by linarith [h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]) (pow_pos h.1 2)
  have hS : 0 < ∑ i, B.upper i / B.mass i ^ 2 :=
    Finset.sum_pos (fun i _ => hterm i) Finset.univ_nonempty
  set m0 := min (nu0 / 2) ((θ / 2) ^ (planetaryDriftExponent n)⁻¹) with hm0
  have hm0pos : 0 < m0 :=
    lt_min (half_pos hnu0) (Real.rpow_pos_of_pos (half_pos hθ) _)
  refine ⟨B0⁻¹ * m0, B0 ^ (-planetaryTimeExponent n),
    B0 ^ planetaryDriftExponent n * ∑ i, B.upper i / B.mass i ^ 2,
    mul_pos (inv_pos.2 hB0pos) hm0pos, Real.rpow_pos_of_pos hB0pos _,
    mul_pos (Real.rpow_pos_of_pos hB0pos _) hS, ?_⟩
  -- `stepP:p14:es-par`: the parameters `nu = B0 * mu`, `T`, `delta`.
  intro mu hmu hmuStar z0 hz0
  have hnu : 0 < B0 * mu := mul_pos hB0pos hmu
  have hnum0 : B0 * mu < m0 := by
    have := mul_lt_mul_of_pos_left hmuStar hB0pos
    rwa [← mul_assoc, mul_inv_cancel₀ hB0pos.ne', one_mul] at this
  have hnunu0 : B0 * mu < nu0 := hnum0.trans_le ((min_le_left _ _).trans (half_le_self hnu0.le))
  have hnu1 : B0 * mu ≤ 1 := hnunu0.le.trans hnu01
  have hnub : (B0 * mu) ^ planetaryDriftExponent n < θ / 2 := by
    have h := Real.rpow_lt_rpow hnu.le (hnum0.trans_le (min_le_right _ _)) hb
    rwa [Real.rpow_inv_rpow (half_pos hθ).le hb.ne'] at h
  have hTeq : Real.exp (B0 ^ (-planetaryTimeExponent n) * mu ^ (-planetaryTimeExponent n)) =
      Real.exp ((B0 * mu) ^ (-planetaryTimeExponent n)) := by
    rw [Real.mul_rpow hB0pos.le hmu.le]
  have hTle : Real.exp (B0 ^ (-planetaryTimeExponent n) * mu ^ (-planetaryTimeExponent n)) ≤
      (B0 * mu)⁻¹ * Real.exp ((B0 * mu) ^ (-planetaryTimeExponent n)) := by
    rw [hTeq]
    exact le_mul_of_one_le_left (Real.exp_pos _).le (one_le_inv₀ hnu |>.2 hnu1)
  have hdelta : 0 < (B0 * mu) ^ planetaryDriftExponent n / 2 :=
    half_pos (Real.rpow_pos_of_pos hnu _)
  -- `stepP:p14:es-stop`: the stopped bound at these parameters.
  have hstopB := hst mu _ _ hmu hnunu0 (Real.exp_pos _) hdelta hTle le_rfl z0
  -- `stepP:p14:es-amd`: the collar margins and the deterministic helper `amd`.
  have hmargin : ∀ i, B.lower i + 2 * ((B0 * mu) ^ planetaryDriftExponent n / 2) <
      B.innerLower i ∧ B.innerUpper i + 2 * ((B0 * mu) ^ planetaryDriftExponent n / 2) <
      B.upper i := fun i => by
    have h := hθi i
    constructor <;> linarith
  have hAMD : B.initialAMD + 2 * (n : ℝ) * ((B0 * mu) ^ planetaryDriftExponent n / 2) <
      B.outerAMD := by
    have h : (n : ℝ) * (B0 * mu) ^ planetaryDriftExponent n < (n : ℝ) * θ :=
      mul_lt_mul_of_pos_left (hnub.trans (half_lt_self hθ)) hnpos
    linarith
  obtain ⟨z, hz0', hgroup, hdrift⟩ :=
    amd hn B hB mu _ _ hmu (Real.exp_pos _) hdelta hmargin hAMD z0 hz0 hstopB
  -- `stepP:p14:es-assemble` and `stepP:p14:es-axis`.
  refine ⟨z, hz0', hgroup, fun t ht i => ?_⟩
  have htI := abs_le.1 ht
  have hzt := ((hgroup.2.2.2 t htI).1).2.1 i
  have hz0i := hz0.2.1 i
  have hBi := hB.1 i
  have hax := keplerAxis_drift_le (u := B.upper i) hBi.1
    (by linarith [hBi.2.1, hzt.1]) hzt.2 (by linarith [hBi.2.1, hBi.2.2.1, hz0i.1])
    (by linarith [hz0i.2, hBi.2.2.2.2]) ((hdrift t htI).2 i)
  have hsingle : B.upper i / B.mass i ^ 2 ≤ ∑ j, B.upper j / B.mass j ^ 2 :=
    Finset.single_le_sum (fun j _ => (hterm j).le) (Finset.mem_univ i)
  calc |keplerAxis B.mass (z t) i - keplerAxis B.mass z0 i|
      ≤ 2 * (B.upper i / B.mass i ^ 2) * ((B0 * mu) ^ planetaryDriftExponent n / 2) := hax
    _ = B0 ^ planetaryDriftExponent n * (B.upper i / B.mass i ^ 2) *
          mu ^ planetaryDriftExponent n := by
        rw [Real.mul_rpow hB0pos.le hmu.le]
        ring
    _ ≤ B0 ^ planetaryDriftExponent n * (∑ j, B.upper j / B.mass j ^ 2) *
          mu ^ planetaryDriftExponent n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsingle (Real.rpow_pos_of_pos hB0pos _).le)
          (Real.rpow_pos_of_pos hmu _).le

end KAM.Planetary

end
