/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Momentum
public import KAM.Planetary.StrongAMD.Osculating.Core

/-!
# Specific Kepler elements with parameter `k` in dimension three and their perturbation estimates

Package LP-SP-OSC, `LP:MAIN L16 (508–529)` with `d = 3` and amendment N10; track LP, non-frozen. The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For a position `q`, a velocity `V` and a gravitational parameter `k` (`Fin 3` vectors, unit mass), the
specific elements of `LP:MAIN L16 (42)`:
`spatialSpecEnergy k q V = |V|²/2 - k/|q|`, `spatialSpecAxis = -k/(2 E)`,
`spatialSpecEccVector k q V = ((|V|² - k/|q|) q - (q·V) V)/k`.

This is the `Fin 3` twin of `KAM.Planetary.StrongAMD.Osculating.Estimates`; the scalar algebra
(`abs_specAxis_sub_le`, `abs_peri_apo_sub_le`, the constants `oscAE`, …) is dimension free and is
reused from the planar package.

* `spatialSpecAxis_tangency`: Lemma 2 with parameter `k` (the ellipse passes through `q`), via
  `orbital_scalar`, with `|C| = √k |q × V|`.
* `abs_spatialSpecEnergy_sub_le`, `spaceLength_specEccVector_sub_le`: the perturbation estimates behind (43).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD

/-- Specific energy `|V|²/2 - k/|q|` (`LP:MAIN L16 (42)`, `d = 3`). -/
def spatialSpecEnergy (k : ℝ) (q V : Fin 3 → ℝ) : ℝ := spaceSq V / 2 - k / spaceLength q

/-- Semi-major axis `-k/(2E)` (`LP:MAIN L16 (42)`, `d = 3`). -/
def spatialSpecAxis (k : ℝ) (q V : Fin 3 → ℝ) : ℝ := -k / (2 * spatialSpecEnergy k q V)

/-- Eccentricity vector `((|V|² - k/|q|) q - (q·V) V)/k` (`LP:MAIN L16 (42)`, `d = 3`). -/
def spatialSpecEccVector (k : ℝ) (q V : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 / k) • ((spaceSq V - k / spaceLength q) • q - spaceDot q V • V)

/-! ### Euclidean helpers -/

theorem spaceSq_sub_spaceSq (V v : Fin 3 → ℝ) :
    spaceSq V - spaceSq v = spaceDot (V - v) (V + v) := by
  simp only [spaceSq_def, spaceDot_def, Pi.sub_apply, Pi.add_apply]; ring

theorem spaceLength_sub_le_add (a b : Fin 3 → ℝ) :
    spaceLength (a - b) ≤ spaceLength a + spaceLength b := by
  have := spaceLength_add_le a (-b)
  rwa [spaceLength_neg, ← sub_eq_add_neg] at this

theorem abs_spaceSq_sub_le (V v : Fin 3 → ℝ) :
    |spaceSq V - spaceSq v| ≤ spaceLength (V - v) * (spaceLength V + spaceLength v) := by
  rw [spaceSq_sub_spaceSq]
  refine (abs_spaceDot_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (spaceLength_add_le V v) (spaceLength_nonneg _)

/-- Reverse triangle inequality for the Euclidean length. -/
theorem abs_spaceLength_sub_spaceLength_le (v w : Fin 3 → ℝ) :
    |spaceLength v - spaceLength w| ≤ spaceLength (v - w) := by
  rw [abs_le]
  have h1 := spaceLength_add_le (v - w) w
  have h2 := spaceLength_add_le (w - v) v
  rw [sub_add_cancel] at h1 h2
  rw [spaceLength_sub_comm w v] at h2
  constructor <;> linarith

/-! ### Tangency (Lemma 2 with parameter `k`) -/

/-- The squared length of the `k`-eccentricity vector (Lagrange's identity). -/
theorem spaceSq_spatialSpecEccVector {k : ℝ} {q V : Fin 3 → ℝ} (hk : 0 < k)
    (hr : 0 < spaceLength q) :
    spaceSq (spatialSpecEccVector k q V) =
      1 + 2 * spatialSpecEnergy k q V * spaceSq (spaceCross q V) / k ^ 2 := by
  have hq : spaceLength q ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 := by
    rw [spaceLength_sq, spaceSq_def]
  have hne : spaceLength q ≠ 0 := hr.ne'
  have hk0 : k ≠ 0 := hk.ne'
  set r := spaceLength q with hrdef
  set t := k / r with htdef
  have hrt : r ^ 2 * t ^ 2 = k ^ 2 := by rw [htdef]; field_simp
  have hF : spaceSq ((spaceSq V - t) • q - spaceDot q V • V) =
      (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) * t ^ 2 +
        spaceSq (spaceCross q V) * (2 * (spaceSq V - t) - spaceSq V) := by
    simp only [spaceSq_def, spaceDot_def, spaceCross_apply_zero, spaceCross_apply_one,
      spaceCross_apply_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsc : spaceSq (spatialSpecEccVector k q V) =
      (1 / k) ^ 2 * spaceSq ((spaceSq V - t) • q - spaceDot q V • V) := by
    simp only [spatialSpecEccVector, spaceSq_def, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsc, hF, ← hq, hrt]
  unfold spatialSpecEnergy
  rw [← htdef]
  field_simp
  ring

/-- The radial component `q · 𝐞 = |q × V|²/k - |q|` of the `k`-eccentricity vector. -/
theorem spaceDot_spatialSpecEccVector {k : ℝ} {q V : Fin 3 → ℝ} (hk : 0 < k)
    (hr : 0 < spaceLength q) :
    spaceDot q (spatialSpecEccVector k q V) = spaceSq (spaceCross q V) / k - spaceLength q := by
  have hq : spaceLength q ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 := by
    rw [spaceLength_sq, spaceSq_def]
  have hne : spaceLength q ≠ 0 := hr.ne'
  have hk0 : k ≠ 0 := hk.ne'
  set r := spaceLength q with hrdef
  set t := k / r with htdef
  have hrt : r ^ 2 * t = k * r := by rw [htdef]; field_simp
  have hF : spaceDot q ((spaceSq V - t) • q - spaceDot q V • V) =
      (spaceSq V - t) * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) -
        (spaceSq V * (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) - spaceSq (spaceCross q V)) := by
    simp only [spaceSq_def, spaceDot_def, spaceCross_apply_zero, spaceCross_apply_one,
      spaceCross_apply_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsc : spaceDot q (spatialSpecEccVector k q V) =
      (1 / k) * spaceDot q ((spaceSq V - t) • q - spaceDot q V • V) := by
    simp only [spatialSpecEccVector, spaceDot_def, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsc, hF, ← hq]
  have : (spaceSq V - t) * r ^ 2 - (spaceSq V * r ^ 2 - spaceSq (spaceCross q V)) =
      spaceSq (spaceCross q V) - k * r := by linear_combination (-1) * hrt
  rw [this]
  field_simp

/-- **Lemma 2 with parameter `k`, `d = 3`** (`LP:MAIN L16 (527)`): for `k > 0`, `|q| > 0` and
negative specific energy, `a (1 - e) ≤ |q| ≤ a (1 + e)` with `a = spatialSpecAxis`,
`e = |spatialSpecEccVector|`. -/
theorem spatialSpecAxis_tangency {k : ℝ} {q V : Fin 3 → ℝ} (hk : 0 < k) (hr : 0 < spaceLength q)
    (hE : spatialSpecEnergy k q V < 0) :
    0 < spatialSpecAxis k q V ∧
    spatialSpecAxis k q V * (1 - spaceLength (spatialSpecEccVector k q V)) ≤ spaceLength q ∧
    spaceLength q ≤ spatialSpecAxis k q V * (1 + spaceLength (spatialSpecEccVector k q V)) := by
  have hsk : (Real.sqrt k) ^ 2 = k := Real.sq_sqrt hk.le
  have hs : 0 ≤ k * spaceSq V := mul_nonneg hk.le (spaceSq_nonneg V)
  have hEdef : spatialSpecEnergy k q V = k * spaceSq V / (2 * k) - k / spaceLength q := by
    unfold spatialSpecEnergy; field_simp
  have hC2 : (Real.sqrt k * spaceLength (spaceCross q V)) ^ 2 = k * spaceSq (spaceCross q V) := by
    rw [mul_pow, hsk, spaceLength_sq]
  have hecc2 : spaceSq (spatialSpecEccVector k q V) =
      1 + 2 * spatialSpecEnergy k q V * (Real.sqrt k * spaceLength (spaceCross q V)) ^ 2 / k ^ 3 := by
    rw [spaceSq_spatialSpecEccVector hk hr, hC2]
    field_simp
  have hdot2 : spaceDot q (spatialSpecEccVector k q V) =
      (Real.sqrt k * spaceLength (spaceCross q V)) ^ 2 / k ^ 2 - spaceLength q := by
    rw [spaceDot_spatialSpecEccVector hk hr, hC2]
    field_simp
  have hnn := spaceLength_nonneg (spatialSpecEccVector k q V)
  have hD := abs_spaceDot_le q (spatialSpecEccVector k q V)
  have hsq := spaceLength_sq (spatialSpecEccVector k q V)
  have := orbital_scalar (μ := k) (r := spaceLength q) (s := k * spaceSq V)
    (C := Real.sqrt k * spaceLength (spaceCross q V)) (E := spatialSpecEnergy k q V)
    (a := spatialSpecAxis k q V) (Λ := k * Real.sqrt (spatialSpecAxis k q V))
    (S := spaceSq (spatialSpecEccVector k q V)) (D := spaceDot q (spatialSpecEccVector k q V))
    (ε := spaceLength (spatialSpecEccVector k q V))
    hk hr hs hE hEdef rfl rfl hecc2 hsq hdot2 hnn hD
  exact ⟨this.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1⟩

/-! ### Perturbation estimates -/

section Estimates

variable {k μ D Pv R dS : ℝ} {q v V : Fin 3 → ℝ}

theorem spaceLength_le_of_sub {v V : Fin 3 → ℝ} {Pv δ : ℝ} (hv : spaceLength v ≤ Pv)
    (hVv : spaceLength (V - v) ≤ δ) : spaceLength V ≤ Pv + δ := by
  have := spaceLength_add_le v (V - v)
  rw [add_sub_cancel] at this
  linarith

/-- Bound on `|V|² - |v|²`. -/
theorem abs_spaceSq_sub_le_of_sub (hv : spaceLength v ≤ Pv) (hVv : spaceLength (V - v) ≤ μ * D)
    (hμ1 : μ ≤ 1) (hμ0 : 0 ≤ μ) (hD : 0 ≤ D) :
    |spaceSq V - spaceSq v| ≤ μ * (D * (2 * Pv + D)) := by
  have hV : spaceLength V ≤ Pv + D := by
    have := spaceLength_le_of_sub hv hVv
    nlinarith
  have h1 := abs_spaceSq_sub_le V v
  have hsum : spaceLength V + spaceLength v ≤ 2 * Pv + D := by linarith
  calc |spaceSq V - spaceSq v|
      ≤ spaceLength (V - v) * (spaceLength V + spaceLength v) := h1
    _ ≤ (μ * D) * (2 * Pv + D) :=
        mul_le_mul hVv hsum (add_nonneg (spaceLength_nonneg _) (spaceLength_nonneg _))
          (mul_nonneg hμ0 hD)
    _ = μ * (D * (2 * Pv + D)) := by ring

theorem abs_spatialSpecEnergy_sub_le (hdS : 0 < dS) (hr : dS ≤ spaceLength q)
    (hv : spaceLength v ≤ Pv) (hVv : spaceLength (V - v) ≤ μ * D) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hD : 0 ≤ D) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ) :
    |spatialSpecEnergy k q V - spatialSpecEnergy 1 q v| ≤ μ * (D * (2 * Pv + D) / 2 + 1 / dS) := by
  have hdiff : spatialSpecEnergy k q V - spatialSpecEnergy 1 q v =
      (spaceSq V - spaceSq v) / 2 - (k - 1) / spaceLength q := by
    unfold spatialSpecEnergy; ring
  have h1 := abs_spaceSq_sub_le_of_sub hv hVv hμ1 hμ0 hD
  have hrpos : 0 < spaceLength q := hdS.trans_le hr
  have h2 : |(k - 1) / spaceLength q| ≤ μ / dS := by
    rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ k - 1), abs_of_pos hrpos]
    exact div_le_div₀ hμ0 hk hdS hr
  rw [hdiff]
  rw [abs_le] at h1 h2 ⊢
  have e1 : μ * (D * (2 * Pv + D) / 2 + 1 / dS) = μ * (D * (2 * Pv + D)) / 2 + μ / dS := by ring
  rw [e1]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The vector `F` of the eccentricity vector: `spatialSpecEccVector k q V = (1/k) • F`. -/
theorem spatialSpecEccVector_eq (k : ℝ) (q V : Fin 3 → ℝ) :
    spatialSpecEccVector k q V = (1 / k) • ((spaceSq V - k / spaceLength q) • q - spaceDot q V • V) :=
  rfl

theorem spaceLength_eccNumerator_sub_le (hdS : 0 < dS) (hr : dS ≤ spaceLength q) (hrR : spaceLength q ≤ R)
    (hv : spaceLength v ≤ Pv) (hVv : spaceLength (V - v) ≤ μ * D) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ) :
    spaceLength (((spaceSq V - k / spaceLength q) • q - spaceDot q V • V) -
        ((spaceSq v - 1 / spaceLength q) • q - spaceDot q v • v)) ≤
      μ * (R * (D * (4 * Pv + 2 * D) + 1 / dS)) := by
  have hrpos : 0 < spaceLength q := hdS.trans_le hr
  have hR0 : 0 ≤ R := hrpos.le.trans hrR
  have hsplit : ((spaceSq V - k / spaceLength q) • q - spaceDot q V • V) -
      ((spaceSq v - 1 / spaceLength q) • q - spaceDot q v • v) =
      ((spaceSq V - spaceSq v) - (k - 1) / spaceLength q) • q -
        (spaceDot q (V - v) • V + spaceDot q v • (V - v)) := by
    ext c
    simp only [spaceDot_def, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hsplit]
  -- first part
  have hA : |(spaceSq V - spaceSq v) - (k - 1) / spaceLength q| ≤
      μ * (D * (2 * Pv + D)) + μ / dS := by
    have h1 := abs_spaceSq_sub_le_of_sub hv hVv hμ1 hμ0 hD
    have h2 : |(k - 1) / spaceLength q| ≤ μ / dS := by
      rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ k - 1), abs_of_pos hrpos]
      exact div_le_div₀ hμ0 hk hdS hr
    calc _ ≤ |spaceSq V - spaceSq v| + |(k - 1) / spaceLength q| := abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  have hfirst : spaceLength (((spaceSq V - spaceSq v) - (k - 1) / spaceLength q) • q) ≤
      (μ * (D * (2 * Pv + D)) + μ / dS) * R := by
    rw [spaceLength_smul]
    exact mul_le_mul hA hrR (spaceLength_nonneg _) (by positivity)
  -- second part
  have hV : spaceLength V ≤ Pv + D := by
    have := spaceLength_le_of_sub hv hVv
    nlinarith
  have hd1 : |spaceDot q (V - v)| ≤ R * (μ * D) :=
    (abs_spaceDot_le _ _).trans (mul_le_mul hrR hVv (spaceLength_nonneg _) hR0)
  have hd2 : |spaceDot q v| ≤ R * Pv :=
    (abs_spaceDot_le _ _).trans (mul_le_mul hrR hv (spaceLength_nonneg _) hR0)
  have hsecond : spaceLength (spaceDot q (V - v) • V + spaceDot q v • (V - v)) ≤
      R * (μ * D) * (Pv + D) + R * Pv * (μ * D) := by
    refine (spaceLength_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [spaceLength_smul]
      exact mul_le_mul hd1 hV (spaceLength_nonneg _) (by positivity)
    · rw [spaceLength_smul]
      exact mul_le_mul hd2 hVv (spaceLength_nonneg _) (by positivity)
  refine (spaceLength_sub_le_add _ _).trans ?_
  have := add_le_add hfirst hsecond
  refine this.trans (le_of_eq ?_)
  ring

theorem spaceLength_spatialSpecEccVector_sub_le (hdS : 0 < dS) (hr : dS ≤ spaceLength q)
    (hrR : spaceLength q ≤ R) (hv : spaceLength v ≤ Pv) (hVv : spaceLength (V - v) ≤ μ * D)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hD : 0 ≤ D) (hPv : 0 ≤ Pv) (hk1 : 1 ≤ k) (hk : k - 1 ≤ μ)
    (he0 : spaceLength (spatialSpecEccVector 1 q v) ≤ 1) :
    spaceLength (spatialSpecEccVector k q V - spatialSpecEccVector 1 q v) ≤
      μ * (R * (D * (4 * Pv + 2 * D) + 1 / dS) + 1) := by
  have hF := spaceLength_eccNumerator_sub_le hdS hr hrR hv hVv hμ0 hμ1 hD hPv hk1 hk
  set F1 := (spaceSq V - k / spaceLength q) • q - spaceDot q V • V with hF1
  set F0 := (spaceSq v - 1 / spaceLength q) • q - spaceDot q v • v with hF0
  have h0 : spatialSpecEccVector 1 q v = F0 := by
    rw [spatialSpecEccVector_eq, hF0, one_div_one, one_smul]
  have hsplit : spatialSpecEccVector k q V - spatialSpecEccVector 1 q v =
      (1 / k) • (F1 - F0) + (1 / k - 1) • F0 := by
    rw [spatialSpecEccVector_eq, h0, ← hF1]
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
  have hF0' : spaceLength F0 ≤ 1 := h0 ▸ he0
  rw [hsplit]
  refine (spaceLength_add_le _ _).trans ?_
  rw [spaceLength_smul, spaceLength_smul, abs_of_nonneg hk'0]
  have t1 : 1 / k * spaceLength (F1 - F0) ≤ μ * (R * (D * (4 * Pv + 2 * D) + 1 / dS)) :=
    (mul_le_of_le_one_left (spaceLength_nonneg _) hk').trans hF
  have t2 : |1 / k - 1| * spaceLength F0 ≤ μ * 1 :=
    mul_le_mul hkk hF0' (spaceLength_nonneg _) hμ0
  nlinarith

end Estimates

end KAM.Planetary.Spatial

end
