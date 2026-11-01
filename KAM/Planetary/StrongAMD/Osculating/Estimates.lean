/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Planetary.StrongAMD.Orbital

/-!
# Specific Kepler elements with parameter `k` and their perturbation estimates

Package LP-OSC, `LP:MAIN L16 (508–529)` with amendment N10; track LP, non-frozen; the statement
surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For a position `q`, a velocity `V` and a gravitational parameter `k` (planar, unit mass), the
specific elements of `LP:MAIN L16 (42)`:
`specEnergy k q V = |V|²/2 - k/|q|`, `specAxis = -k/(2 E)`,
`specEccVector k q V = ((|V|² - k/|q|) q - (q·V) V)/k`.

This module is pure vector/real analysis, free of any masses or phases:

* `specAxis_tangency`: Lemma 2 with parameter `k` (the ellipse passes through `q`), via
  `orbital_scalar` of LP-MOM.
* `abs_specEnergy_sub_le`, `planeLength_specEccVector_sub_le`, `abs_specAxis_sub_le`,
  `abs_peri_apo_sub_le`: the perturbation estimates behind (43).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Kepler KAM.Planetary

/-- Specific energy `|V|²/2 - k/|q|` (`LP:MAIN L16 (42)`). -/
def specEnergy (k : ℝ) (q V : Fin 2 → ℝ) : ℝ := planeSq V / 2 - k / planeLength q

/-- Semi-major axis `-k/(2E)` (`LP:MAIN L16 (42)`). -/
def specAxis (k : ℝ) (q V : Fin 2 → ℝ) : ℝ := -k / (2 * specEnergy k q V)

/-- Eccentricity vector `((|V|² - k/|q|) q - (q·V) V)/k` (`LP:MAIN L16 (42)`). -/
def specEccVector (k : ℝ) (q V : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (1 / k) • ((planeSq V - k / planeLength q) • q - planeDot q V • V)

/-! ### Coordinate expansions -/

theorem planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

theorem planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

theorem planeSq_sub_planeSq (V v : Fin 2 → ℝ) :
    planeSq V - planeSq v = planeDot (V - v) (V + v) := by
  simp only [planeSq_two, planeDot_two, Pi.sub_apply, Pi.add_apply]; ring

theorem planeLength_sub_le (a b : Fin 2 → ℝ) :
    planeLength (a - b) ≤ planeLength a + planeLength b := by
  have := planeLength_add_le a (-b)
  rwa [planeLength_neg, ← sub_eq_add_neg] at this

theorem abs_planeSq_sub_le (V v : Fin 2 → ℝ) :
    |planeSq V - planeSq v| ≤ planeLength (V - v) * (planeLength V + planeLength v) := by
  rw [planeSq_sub_planeSq]
  refine (abs_planeDot_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (planeLength_add_le V v) (planeLength_nonneg _)

theorem planeLength_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin 2 → ℝ) :
    planeLength (∑ j ∈ s, f j) ≤ ∑ j ∈ s, planeLength (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : planeLength (0 : Fin 2 → ℝ) = 0 := planeLength_eq_zero_iff.2 rfl
    simp [h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (planeLength_add_le _ _).trans (by linarith)

/-! ### Tangency (Lemma 2 with parameter `k`) -/

/-- The squared length of the `k`-eccentricity vector (Lagrange's identity). -/
theorem planeSq_specEccVector {k : ℝ} {q V : Fin 2 → ℝ} (hk : 0 < k) (hr : 0 < planeLength q) :
    planeSq (specEccVector k q V) = 1 + 2 * specEnergy k q V * planeCross q V ^ 2 / k ^ 2 := by
  have hq : planeLength q ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [KAM.Kepler.planeLength_sq, planeSq_two]
  have hne : planeLength q ≠ 0 := hr.ne'
  have hk0 : k ≠ 0 := hk.ne'
  set r := planeLength q with hrdef
  set t := k / r with htdef
  have hrt : r ^ 2 * t ^ 2 = k ^ 2 := by rw [htdef]; field_simp
  have hF : planeSq ((planeSq V - t) • q - planeDot q V • V) =
      (q 0 ^ 2 + q 1 ^ 2) * t ^ 2 + planeCross q V ^ 2 * (2 * (planeSq V - t) - planeSq V) := by
    simp only [planeSq_two, planeDot_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [planeCross]
    ring
  have hsc : planeSq (specEccVector k q V) =
      (1 / k) ^ 2 * planeSq ((planeSq V - t) • q - planeDot q V • V) := by
    simp only [specEccVector, planeSq_two, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsc, hF, ← hq, hrt]
  unfold specEnergy
  rw [← htdef]
  field_simp
  ring

/-- The radial component `q · e = (q × V)²/k - |q|` of the `k`-eccentricity vector. -/
theorem planeDot_specEccVector {k : ℝ} {q V : Fin 2 → ℝ} (hk : 0 < k) (hr : 0 < planeLength q) :
    planeDot q (specEccVector k q V) = planeCross q V ^ 2 / k - planeLength q := by
  have hq : planeLength q ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [KAM.Kepler.planeLength_sq, planeSq_two]
  have hne : planeLength q ≠ 0 := hr.ne'
  have hk0 : k ≠ 0 := hk.ne'
  set r := planeLength q with hrdef
  set t := k / r with htdef
  have hrt : r ^ 2 * t = k * r := by rw [htdef]; field_simp
  have hF : planeDot q ((planeSq V - t) • q - planeDot q V • V) =
      (planeSq V - t) * (q 0 ^ 2 + q 1 ^ 2) -
        (planeSq V * (q 0 ^ 2 + q 1 ^ 2) - planeCross q V ^ 2) := by
    simp only [planeSq_two, planeDot_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [planeCross]
    ring
  have hsc : planeDot q (specEccVector k q V) =
      (1 / k) * planeDot q ((planeSq V - t) • q - planeDot q V • V) := by
    simp only [specEccVector, planeDot_two, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsc, hF, ← hq]
  have : (planeSq V - t) * r ^ 2 - (planeSq V * r ^ 2 - planeCross q V ^ 2) =
      planeCross q V ^ 2 - k * r := by linear_combination (-1) * hrt
  rw [this]
  field_simp

/-- **Lemma 2 with parameter `k`** (`LP:MAIN L16 (527)`): for `k > 0`, `|q| > 0` and negative
specific energy, `a (1 - e) ≤ |q| ≤ a (1 + e)` with `a = specAxis`, `e = |specEccVector|`. -/
theorem specAxis_tangency {k : ℝ} {q V : Fin 2 → ℝ} (hk : 0 < k) (hr : 0 < planeLength q)
    (hE : specEnergy k q V < 0) :
    0 < specAxis k q V ∧
    specAxis k q V * (1 - planeLength (specEccVector k q V)) ≤ planeLength q ∧
    planeLength q ≤ specAxis k q V * (1 + planeLength (specEccVector k q V)) := by
  have hsk : (Real.sqrt k) ^ 2 = k := Real.sq_sqrt hk.le
  have hs : 0 ≤ k * planeSq V := mul_nonneg hk.le (by rw [← KAM.Kepler.planeLength_sq]; positivity)
  have hEdef : specEnergy k q V = k * planeSq V / (2 * k) - k / planeLength q := by
    unfold specEnergy; field_simp
  have hecc2 : planeSq (specEccVector k q V) =
      1 + 2 * specEnergy k q V * (Real.sqrt k * planeCross q V) ^ 2 / k ^ 3 := by
    rw [planeSq_specEccVector hk hr, mul_pow, hsk]
    field_simp
  have hdot2 : planeDot q (specEccVector k q V) =
      (Real.sqrt k * planeCross q V) ^ 2 / k ^ 2 - planeLength q := by
    rw [planeDot_specEccVector hk hr, mul_pow, hsk]
    field_simp
  have hnn := KAM.Kepler.planeLength_nonneg (specEccVector k q V)
  have hD := KAM.Kepler.abs_planeDot_le q (specEccVector k q V)
  have hsq := KAM.Kepler.planeLength_sq (specEccVector k q V)
  have := orbital_scalar (μ := k) (r := planeLength q) (s := k * planeSq V)
    (C := Real.sqrt k * planeCross q V) (E := specEnergy k q V) (a := specAxis k q V)
    (Λ := k * Real.sqrt (specAxis k q V)) (S := planeSq (specEccVector k q V))
    (D := planeDot q (specEccVector k q V)) (ε := planeLength (specEccVector k q V))
    hk hr hs hE hEdef rfl rfl hecc2 hsq hdot2 hnn hD
  exact ⟨this.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1⟩

/-! ### Perturbation estimates -/

section Estimates

variable {k μ D Pv R dS : ℝ} {q v V : Fin 2 → ℝ}

theorem planeLength_le_of_sub {v V : Fin 2 → ℝ} {Pv δ : ℝ} (hv : planeLength v ≤ Pv)
    (hVv : planeLength (V - v) ≤ δ) : planeLength V ≤ Pv + δ := by
  have := planeLength_add_le v (V - v)
  rw [add_sub_cancel] at this
  linarith

/-- Bound on `|V|² - |v|²`. -/
theorem abs_planeSq_sub_le' (hv : planeLength v ≤ Pv) (hVv : planeLength (V - v) ≤ μ * D)
    (hμ1 : μ ≤ 1) (hμ0 : 0 ≤ μ) (hD : 0 ≤ D) :
    |planeSq V - planeSq v| ≤ μ * (D * (2 * Pv + D)) := by
  have hV : planeLength V ≤ Pv + D := by
    have := planeLength_le_of_sub hv hVv
    nlinarith
  have h1 := abs_planeSq_sub_le V v
  have hsum : planeLength V + planeLength v ≤ 2 * Pv + D := by linarith
  calc |planeSq V - planeSq v|
      ≤ planeLength (V - v) * (planeLength V + planeLength v) := h1
    _ ≤ (μ * D) * (2 * Pv + D) :=
        mul_le_mul hVv hsum (add_nonneg (planeLength_nonneg _) (planeLength_nonneg _))
          (mul_nonneg hμ0 hD)
    _ = μ * (D * (2 * Pv + D)) := by ring

theorem abs_specEnergy_sub_le (hdS : 0 < dS) (hr : dS ≤ planeLength q)
    (hv : planeLength v ≤ Pv) (hVv : planeLength (V - v) ≤ μ * D) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hD : 0 ≤ D) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ) :
    |specEnergy k q V - specEnergy 1 q v| ≤ μ * (D * (2 * Pv + D) / 2 + 1 / dS) := by
  have hdiff : specEnergy k q V - specEnergy 1 q v =
      (planeSq V - planeSq v) / 2 - (k - 1) / planeLength q := by
    unfold specEnergy; ring
  have h1 := abs_planeSq_sub_le' hv hVv hμ1 hμ0 hD
  have hrpos : 0 < planeLength q := hdS.trans_le hr
  have h2 : |(k - 1) / planeLength q| ≤ μ / dS := by
    rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ k - 1), abs_of_pos hrpos]
    exact div_le_div₀ hμ0 hk hdS hr
  rw [hdiff]
  rw [abs_le] at h1 h2 ⊢
  have e1 : μ * (D * (2 * Pv + D) / 2 + 1 / dS) = μ * (D * (2 * Pv + D)) / 2 + μ / dS := by ring
  rw [e1]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The vector `F` of the eccentricity vector: `specEccVector k q V = (1/k) • F`. -/
theorem specEccVector_eq (k : ℝ) (q V : Fin 2 → ℝ) :
    specEccVector k q V = (1 / k) • ((planeSq V - k / planeLength q) • q - planeDot q V • V) :=
  rfl

theorem planeLength_F_sub_le (hdS : 0 < dS) (hr : dS ≤ planeLength q) (hrR : planeLength q ≤ R)
    (hv : planeLength v ≤ Pv) (hVv : planeLength (V - v) ≤ μ * D) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ) :
    planeLength (((planeSq V - k / planeLength q) • q - planeDot q V • V) -
        ((planeSq v - 1 / planeLength q) • q - planeDot q v • v)) ≤
      μ * (R * (D * (4 * Pv + 2 * D) + 1 / dS)) := by
  have hrpos : 0 < planeLength q := hdS.trans_le hr
  have hR0 : 0 ≤ R := hrpos.le.trans hrR
  have hsplit : ((planeSq V - k / planeLength q) • q - planeDot q V • V) -
      ((planeSq v - 1 / planeLength q) • q - planeDot q v • v) =
      ((planeSq V - planeSq v) - (k - 1) / planeLength q) • q -
        (planeDot q (V - v) • V + planeDot q v • (V - v)) := by
    ext c
    simp only [planeDot_two, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hsplit]
  -- first part
  have hA : |(planeSq V - planeSq v) - (k - 1) / planeLength q| ≤
      μ * (D * (2 * Pv + D)) + μ / dS := by
    have h1 := abs_planeSq_sub_le' hv hVv hμ1 hμ0 hD
    have h2 : |(k - 1) / planeLength q| ≤ μ / dS := by
      rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ k - 1), abs_of_pos hrpos]
      exact div_le_div₀ hμ0 hk hdS hr
    calc _ ≤ |planeSq V - planeSq v| + |(k - 1) / planeLength q| := abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  have hfirst : planeLength (((planeSq V - planeSq v) - (k - 1) / planeLength q) • q) ≤
      (μ * (D * (2 * Pv + D)) + μ / dS) * R := by
    rw [planeLength_smul]
    exact mul_le_mul hA hrR (planeLength_nonneg _) (by positivity)
  -- second part
  have hV : planeLength V ≤ Pv + D := by
    have := planeLength_le_of_sub hv hVv
    nlinarith
  have hd1 : |planeDot q (V - v)| ≤ R * (μ * D) :=
    (abs_planeDot_le _ _).trans (mul_le_mul hrR hVv (planeLength_nonneg _) hR0)
  have hd2 : |planeDot q v| ≤ R * Pv :=
    (abs_planeDot_le _ _).trans (mul_le_mul hrR hv (planeLength_nonneg _) hR0)
  have hsecond : planeLength (planeDot q (V - v) • V + planeDot q v • (V - v)) ≤
      R * (μ * D) * (Pv + D) + R * Pv * (μ * D) := by
    refine (planeLength_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [planeLength_smul]
      exact mul_le_mul hd1 hV (planeLength_nonneg _) (by positivity)
    · rw [planeLength_smul]
      exact mul_le_mul hd2 hVv (planeLength_nonneg _) (by positivity)
  refine (planeLength_sub_le _ _).trans ?_
  have := add_le_add hfirst hsecond
  refine this.trans (le_of_eq ?_)
  ring

theorem planeLength_specEccVector_sub_le (hdS : 0 < dS) (hr : dS ≤ planeLength q)
    (hrR : planeLength q ≤ R) (hv : planeLength v ≤ Pv) (hVv : planeLength (V - v) ≤ μ * D)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ)
    (he0 : planeLength (specEccVector 1 q v) ≤ 1) :
    planeLength (specEccVector k q V - specEccVector 1 q v) ≤
      μ * (R * (D * (4 * Pv + 2 * D) + 1 / dS) + 1) := by
  have hF := planeLength_F_sub_le hdS hr hrR hv hVv hμ0 hμ1 hD hPv hk1 hk
  set F1 := (planeSq V - k / planeLength q) • q - planeDot q V • V with hF1
  set F0 := (planeSq v - 1 / planeLength q) • q - planeDot q v • v with hF0
  have h0 : specEccVector 1 q v = F0 := by
    rw [specEccVector_eq, hF0, one_div_one, one_smul]
  have hsplit : specEccVector k q V - specEccVector 1 q v =
      (1 / k) • (F1 - F0) + (1 / k - 1) • F0 := by
    rw [specEccVector_eq, h0, ← hF1]
    module
  have hkpos : 0 < k := by linarith
  have hk' : 1 / k ≤ 1 := by rw [div_le_one hkpos]; exact hk1
  have hk'0 : 0 ≤ 1 / k := by positivity
  have hkk : |1 / k - 1| ≤ μ := by
    rw [abs_le]
    constructor
    · have : 1 / k - 1 = -(k - 1) / k := by field_simp; ring
      rw [this, le_div_iff₀ hkpos]
      nlinarith
    · linarith
  have hF0' : planeLength F0 ≤ 1 := h0 ▸ he0
  rw [hsplit]
  refine (planeLength_add_le _ _).trans ?_
  rw [planeLength_smul, planeLength_smul, abs_of_nonneg hk'0]
  have t1 : 1 / k * planeLength (F1 - F0) ≤ μ * (R * (D * (4 * Pv + 2 * D) + 1 / dS)) :=
    (mul_le_of_le_one_left (planeLength_nonneg _) hk').trans hF
  have t2 : |1 / k - 1| * planeLength F0 ≤ μ * 1 :=
    mul_le_mul hkk hF0' (planeLength_nonneg _) hμ0
  nlinarith

/-- Axis estimate from the difference of two reciprocals. -/
theorem abs_specAxis_sub_le {k E1 E0 AE B c1 : ℝ} (hc1 : 0 < c1) (hE0 : E0 ≤ -c1)
    (hE1 : E1 ≤ -(c1 / 2)) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ) (hμ0 : 0 ≤ μ)
    (hAE : 0 ≤ AE) (hB0 : 0 ≤ B) (hE : |E1 - E0| ≤ μ * AE) (hB : |E0| ≤ B) :
    |(-k / (2 * E1)) - (-1 / (2 * E0))| ≤ μ * ((AE + B) / c1 ^ 2) := by
  have hE1n : E1 < 0 := by linarith
  have hE0n : E0 < 0 := by linarith
  have hdiff : (-k / (2 * E1)) - (-1 / (2 * E0)) = (E1 - k * E0) / (2 * E1 * E0) := by
    have := hE1n.ne
    have := hE0n.ne
    field_simp
    ring
  have hden : c1 ^ 2 ≤ 2 * E1 * E0 := by
    have h1 : c1 / 2 ≤ -E1 := by linarith
    have h2 : c1 ≤ -E0 := by linarith
    have := mul_le_mul h1 h2 hc1.le (by linarith)
    nlinarith
  have hnum : |E1 - k * E0| ≤ μ * (AE + B) := by
    have : E1 - k * E0 = (E1 - E0) - (k - 1) * E0 := by ring
    rw [this]
    have h3 : |(k - 1) * E0| ≤ μ * B := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ k - 1)]
      exact mul_le_mul hk hB (abs_nonneg _) hμ0
    calc _ ≤ |E1 - E0| + |(k - 1) * E0| := abs_sub _ _
      _ ≤ μ * AE + μ * B := add_le_add hE h3
      _ = _ := by ring
  rw [hdiff, abs_div, abs_of_pos (by nlinarith : 0 < 2 * E1 * E0)]
  rw [div_le_iff₀ (by nlinarith : 0 < 2 * E1 * E0)]
  have hc2 : 0 < c1 ^ 2 := by positivity
  have : μ * ((AE + B) / c1 ^ 2) * (2 * E1 * E0) ≥ μ * ((AE + B) / c1 ^ 2) * c1 ^ 2 := by
    have hnn : 0 ≤ μ * ((AE + B) / c1 ^ 2) :=
      mul_nonneg hμ0 (div_nonneg (by linarith) (sq_nonneg _))
    exact mul_le_mul_of_nonneg_left hden hnn
  have e2 : μ * ((AE + B) / c1 ^ 2) * c1 ^ 2 = μ * (AE + B) := by field_simp
  linarith

end Estimates

end KAM.Planetary.StrongAMD

end
