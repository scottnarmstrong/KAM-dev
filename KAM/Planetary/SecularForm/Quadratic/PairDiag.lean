/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.PairLocal
public import KAM.Planetary.SecularForm.Quadratic.Calculus
public import KAM.Planetary.SecularForm.DiagonalJet
public import KAM.Planetary.SecularForm.Coefficients

/-!
# Quadratic part: the diagonal second derivatives of the pair average

Blueprint P, Part 8, `stepP:p8:qf-diag` and `stepP:p8:qf-assembly` (package S8-Q). The second
derivative of the pair average along the rays `s ↦ (s u, 0)` and `s ↦ (0, s v)` is `-2 pairA/Λ`
times the squared length, from the diagonal jet `pairSlowSecular_diag_jet` of S8-D and the exchange
of the two planets.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

/-- A function that is `A + c s² + A₄ s⁴ + O(|s L|⁶)` has second derivative `2c`. -/
theorem iteratedDeriv_two_of_expansion {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0)
    {A c A4 C L r : ℝ} (hL : 0 ≤ L) (hr : 0 < r)
    (h : ∀ s : ℝ, |s| * L < r → |φ s - (A + c * s ^ 2 + A4 * s ^ 4)| ≤ C * (|s| * L) ^ 6) :
    iteratedDeriv 2 φ 0 = 2 * c := by
  have hε : 0 < min 1 (r / (L + 1)) := lt_min one_pos (by positivity)
  refine iteratedDeriv_two_of_bound hφ A c (K := |A4| + |C| * L ^ 6) hε fun s hs => ?_
  have hs1 : |s| < 1 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s| < r / (L + 1) := lt_of_lt_of_le hs (min_le_right _ _)
  have hsL : |s| * L < r := by
    have := (lt_div_iff₀ (by positivity : 0 < L + 1)).1 hs2
    nlinarith [abs_nonneg s]
  have hb := h s hsL
  have h3 : 0 ≤ |s| ^ 3 := by positivity
  have h4 : |s| ^ 4 ≤ |s| ^ 3 := by
    have : |s| ^ 4 = |s| ^ 3 * |s| := by ring
    rw [this]; exact mul_le_of_le_one_right h3 hs1.le
  have h6 : |s| ^ 6 ≤ |s| ^ 3 := by
    have : |s| ^ 6 = |s| ^ 3 * |s| ^ 3 := by ring
    rw [this]; exact mul_le_of_le_one_right h3 (pow_le_one₀ (abs_nonneg s) hs1.le)
  have e1 : |A4 * s ^ 4| = |A4| * |s| ^ 4 := by rw [abs_mul, abs_pow]
  have e2 : C * (|s| * L) ^ 6 ≤ |C| * L ^ 6 * |s| ^ 3 := by
    calc C * (|s| * L) ^ 6 ≤ |C| * (|s| * L) ^ 6 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = |C| * L ^ 6 * |s| ^ 6 := by ring
      _ ≤ |C| * L ^ 6 * |s| ^ 3 := mul_le_mul_of_nonneg_left h6 (by positivity)
  have e3 : |A4| * |s| ^ 4 ≤ |A4| * |s| ^ 3 := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  calc |φ s - (A + c * s ^ 2)|
      = |(φ s - (A + c * s ^ 2 + A4 * s ^ 4)) + A4 * s ^ 4| := by ring_nf
    _ ≤ |φ s - (A + c * s ^ 2 + A4 * s ^ 4)| + |A4 * s ^ 4| := abs_add_le _ _
    _ ≤ (|A4| + |C| * L ^ 6) * |s| ^ 3 := by rw [e1]; nlinarith

theorem planeSq_smul' (s : ℝ) (u : Fin 2 → ℝ) : planeSq (s • u) = s ^ 2 * planeSq u := by
  simp [planeSq, Fin.sum_univ_two, mul_pow]
  ring

/-- The second derivative of the pair average along `s ↦ (s u, 0)`. -/
theorem pair_diag_ray (D : Data n) (p q : Fin n) {I J : ℝ} (hI : 0 < I) (hJ : 0 < J)
    (hab : I ^ 2 / (D.m p ^ 2 * (D.G * D.m0)) ≠ J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)))
    (u : Vec 2)
    (hφ : AnalyticAt ℝ (fun s : ℝ => pairSlowSecular D p q I J (s • (u, 0))) 0) :
    iteratedDeriv 2 (fun s : ℝ => pairSlowSecular D p q I J (s • (u, 0))) 0 =
      2 * (-D.G * D.m p * D.m q * (iteratedDeriv 2 (radialH (I ^ 2 / (D.m p ^ 2 * (D.G * D.m0)))
        (J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)))) 0 / 4) * (planeSq u / I)) := by
  obtain ⟨r, C, hr, hC, hbd⟩ := pairSlowSecular_diag_jet D p q hI hJ hab
  set a := I ^ 2 / (D.m p ^ 2 * (D.G * D.m0)) with ha
  set b := J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)) with hb
  set H := radialH a b with hH
  set P := planeSq u with hP
  refine iteratedDeriv_two_of_expansion hφ
    (A := -D.G * D.m p * D.m q * H 0)
    (A4 := -D.G * D.m p * D.m q * (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) *
      (P / I) ^ 2)
    (C := C) (L := planeLength u) (r := r) (planeLength_nonneg u) hr fun s hs => ?_
  have hlen : planeLength (s • u) = |s| * planeLength u := planeLength_smul s u
  have hsq : planeSq (s • u) = s ^ 2 * P := planeSq_smul' s u
  have h := hbd (s • u) (by rw [hlen]; exact hs)
  rw [hlen, hsq] at h
  simp only [Prod.smul_mk, smul_zero]
  convert h using 2
  ring

end SecularForm
end KAM.Planetary
end
