/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.DiagonalJet.Radial
public import KAM.Planetary.SecularForm.DiagonalJet.Orbit
public import KAM.Planetary.SecularForm.DiagonalJet.Pair
public import KAM.Planetary.SecularForm.DiagonalJet.Mean

/-!
# Secular form: the diagonal jet of the pair average

Blueprint P, Part 8: internal proof cuts of `quadratic_form` (`bpP:p8:quadratic-form`) and the
exact diagonal values of the quartic coefficients (`bpP:p8:quartic`), returning identities for
the literal pair average `pairSlowSecular`. Nothing here assumes a coefficient structure or the
quadratic matrix.

* `stepP:p8:qf-scale`: `radialPhi_comm`, `radialPhi_smul`, `radialPhi_eq_laplace`,
  `analyticOnNhd_radialPhi` (`DiagonalJet.Radial`).
* `stepP:p8:qf-c0`: `pairSlowSecular_zero` (`DiagonalJet.Pair`).
* `stepP:p8:qf-diag`: `planeLength_poincare_fst`, `circle_average`,
  `pairSlowSecular_circular_partner` (the orbit average `⟨h(e cos u)⟩`), `circleMean_jet`,
  `iteratedDeriv_two_radialH_of_lt/gt` (the second derivative via the Laplace identities), and
  the assembled jet `pairSlowSecular_diag_jet` below.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- `stepP:p8:qf-diag` and the exact diagonal derivatives: with the second planet circular and
distinct axes `aᵢ ≠ aⱼ`, the literal pair average has the jet
`-G mᵢ mⱼ [h(0) + (h''(0)/4)(|u|²/Λ) + (h⁗(0)/64 - h''(0)/16)(|u|²/Λ)²] + O(|u|⁶)`
in `u = (ξ, η)` of the first planet, where `h = radialH aᵢ aⱼ`. -/
theorem pairSlowSecular_diag_jet (D : Data n) (i j : Fin n) {I J : ℝ} (hI : 0 < I) (hJ : 0 < J)
    (hab : I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) ≠ J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ u : Fin 2 → ℝ, planeLength u < r →
      |pairSlowSecular D i j I J (u, 0) -
        (-D.G * D.m i * D.m j *
          (radialH (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) 0 +
            iteratedDeriv 2 (radialH (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
              (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))) 0 / 4 * (planeSq u / I) +
            (iteratedDeriv 4 (radialH (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
              (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))) 0 / 64 -
              iteratedDeriv 2 (radialH (I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
                (J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))) 0 / 16) * (planeSq u / I) ^ 2))| ≤
        C * planeLength u ^ 6 := by
  set a := I ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) with ha
  set b := J ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) with hb
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have ha0 : 0 < a := div_pos (pow_pos hI 2) (mul_pos (pow_pos (D.hm i) 2) hκ)
  have hb0 : 0 < b := div_pos (pow_pos hJ 2) (mul_pos (pow_pos (D.hm j) 2) hκ)
  have hGm : 0 < D.G * D.m i * D.m j := mul_pos (mul_pos D.hG (D.hm i)) (D.hm j)
  set H := radialH a b with hH
  obtain ⟨rH, CH, hrH, hCH, hjet⟩ := circleMean_jet (analyticAt_radialH ha0 hb0 hab)
  set δ := |a - b| / a with hδ
  have hδ0 : 0 < δ := div_pos (abs_pos.2 (sub_ne_zero.2 hab)) ha0
  have hsI : 0 < √I := Real.sqrt_pos.2 hI
  refine ⟨min (min (√I * δ) (√I * rH)) (√I),
    D.G * D.m i * D.m j * (CH + |iteratedDeriv 4 H 0| / 128) / I ^ 3 + 1,
    lt_min (lt_min (mul_pos hsI hδ0) (mul_pos hsI hrH)) hsI, by positivity, fun u hu => ?_⟩
  set r0 := min (min (√I * δ) (√I * rH)) (√I) with hr0
  have hr0pos : 0 < r0 := lt_min (lt_min (mul_pos hsI hδ0) (mul_pos hsI hrH)) hsI
  have hs_def : planeSq u = planeLength u ^ 2 := (planeLength_sq u).symm
  set s := planeSq u with hs
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hlt : s < r0 ^ 2 := by
    rw [hs_def]; exact pow_lt_pow_left₀ hu (planeLength_nonneg u) two_ne_zero
  have hr0I : r0 ^ 2 ≤ I := by
    calc r0 ^ 2 ≤ (√I) ^ 2 := pow_le_pow_left₀ hr0pos.le (min_le_right _ _) 2
      _ = I := Real.sq_sqrt hI.le
  set t := s / I with ht
  have ht0 : 0 ≤ t := div_nonneg hs0 hI.le
  have hw : (![0, u 0], ![I, u 1]) ∈ poincareDom := by
    simp only [poincareDom, mem_ofPred_eq, poincareGamma, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    refine ⟨hI, ?_⟩
    have : planeSq u = u 0 ^ 2 + u 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
    nlinarith
  obtain ⟨-, -, -, -, hsq, -, -⟩ := poincare_facts hw
  have hK : poincareK (![0, u 0], ![I, u 1]) = 1 - t / 2 := by
    have : planeSq u = u 0 ^ 2 + u 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
    simp only [poincareK, poincareGamma, Matrix.cons_val_zero, Matrix.cons_val_one, ht, hs, this]
    field_simp
  set v := poincareV (![0, u 0], ![I, u 1]) with hv
  set e := planeLength v with he
  have he0 : 0 ≤ e := planeLength_nonneg v
  have he2 : e ^ 2 = t - t ^ 2 / 4 := by
    rw [he, planeLength_sq, hsq, hK]; ring
  have het : e ^ 2 ≤ t := by rw [he2]; nlinarith [sq_nonneg t]
  have htsmall : ∀ ρ : ℝ, 0 ≤ ρ → r0 ≤ √I * ρ → t < ρ ^ 2 := fun ρ hρ hr => by
    have h1 : r0 ^ 2 ≤ I * ρ ^ 2 := by
      calc r0 ^ 2 ≤ (√I * ρ) ^ 2 := pow_le_pow_left₀ hr0pos.le hr 2
        _ = I * ρ ^ 2 := by rw [mul_pow, Real.sq_sqrt hI.le]
    rw [ht, div_lt_iff₀ hI]
    nlinarith
  have heδ : e < δ := by
    have := htsmall δ hδ0.le ((min_le_left _ _).trans (min_le_left _ _))
    exact lt_of_pow_lt_pow_left₀ 2 hδ0.le (lt_of_le_of_lt het this)
  have heH : e < rH := by
    have := htsmall rH hrH.le ((min_le_left _ _).trans (min_le_right _ _))
    exact lt_of_pow_lt_pow_left₀ 2 hrH.le (lt_of_le_of_lt het this)
  have hsep : a * (1 + e) < b ∨ b < a * (1 - e) := by
    have h1 : e * a < |a - b| := by rwa [hδ, lt_div_iff₀ ha0] at heδ
    rcases lt_or_gt_of_ne hab with h | h
    · left; rw [abs_of_neg (sub_neg.2 h)] at h1; linarith
    · right; rw [abs_of_pos (sub_pos.2 h)] at h1; linarith
  rw [pairSlowSecular_circular_partner D i j hJ u hw hsep]
  have hM := hjet v heH
  set H2 := iteratedDeriv 2 H 0 with hH2
  set H4 := iteratedDeriv 4 H 0 with hH4
  set M := (2 * π)⁻¹ * ∫ F in (0:ℝ)..2 * π, H (planeDot v (orbitalUnit F)) with hMdef
  have hTe : |(H 0 + H2 / 4 * e ^ 2 + H4 / 64 * e ^ 4) -
      (H 0 + H2 / 4 * t + (H4 / 64 - H2 / 16) * t ^ 2)| ≤ |H4| / 128 * t ^ 3 := by
    have e4 : e ^ 4 = (t - t ^ 2 / 4) ^ 2 := by rw [← he2]; ring
    have h1 : (H 0 + H2 / 4 * e ^ 2 + H4 / 64 * e ^ 4) -
        (H 0 + H2 / 4 * t + (H4 / 64 - H2 / 16) * t ^ 2) =
        -(H4 / 64) * (t ^ 2 / 4) * (e ^ 2 + t) := by
      rw [e4, he2]; ring
    rw [h1, abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 64),
      abs_of_nonneg (by positivity : 0 ≤ t ^ 2 / 4), abs_of_nonneg (add_nonneg (sq_nonneg e) ht0)]
    have : |H4| / 64 * (t ^ 2 / 4) * (e ^ 2 + t) ≤ |H4| / 64 * (t ^ 2 / 4) * (2 * t) := by
      gcongr; linarith
    calc _ ≤ _ := this
      _ = |H4| / 128 * t ^ 3 := by ring
  have he6 : e ^ 6 ≤ t ^ 3 := by
    calc e ^ 6 = (e ^ 2) ^ 3 := by ring
      _ ≤ t ^ 3 := pow_le_pow_left₀ (by positivity) het 3
  have hmain : |M - (H 0 + H2 / 4 * t + (H4 / 64 - H2 / 16) * t ^ 2)| ≤
      (CH + |H4| / 128) * t ^ 3 := by
    calc _ = |(M - (H 0 + H2 / 4 * e ^ 2 + H4 / 64 * e ^ 4)) +
          ((H 0 + H2 / 4 * e ^ 2 + H4 / 64 * e ^ 4) -
            (H 0 + H2 / 4 * t + (H4 / 64 - H2 / 16) * t ^ 2))| := by ring_nf
      _ ≤ |M - (H 0 + H2 / 4 * e ^ 2 + H4 / 64 * e ^ 4)| + _ := abs_add_le _ _
      _ ≤ CH * e ^ 6 + |H4| / 128 * t ^ 3 := add_le_add hM hTe
      _ ≤ (CH + |H4| / 128) * t ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left he6 hCH.le]
  have hfac : -D.G * D.m i * D.m j * M - -D.G * D.m i * D.m j *
      (H 0 + H2 / 4 * (s / I) + (H4 / 64 - H2 / 16) * (s / I) ^ 2) =
      -(D.G * D.m i * D.m j) * (M - (H 0 + H2 / 4 * t + (H4 / 64 - H2 / 16) * t ^ 2)) := by
    rw [← ht]; ring
  have hu6 : planeLength u ^ 6 = I ^ 3 * t ^ 3 := by
    have : t = planeLength u ^ 2 / I := by rw [ht, hs_def]
    rw [this]; field_simp
  rw [hfac, abs_mul, abs_neg, abs_of_pos hGm, hu6]
  calc D.G * D.m i * D.m j * |M - (H 0 + H2 / 4 * t + (H4 / 64 - H2 / 16) * t ^ 2)|
      ≤ D.G * D.m i * D.m j * ((CH + |H4| / 128) * t ^ 3) := by gcongr
    _ = D.G * D.m i * D.m j * (CH + |H4| / 128) / I ^ 3 * (I ^ 3 * t ^ 3) := by
        field_simp
    _ ≤ (D.G * D.m i * D.m j * (CH + |H4| / 128) / I ^ 3 + 1) * (I ^ 3 * t ^ 3) := by
        gcongr
        linarith

end SecularForm
end KAM.Planetary
end
