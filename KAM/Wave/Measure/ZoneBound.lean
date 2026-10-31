/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Pair

/-!
# W7: the zone estimate (blueprint `bpW:w7:zone`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

`IsFreqPair.zone_measure_le`: for `k ≠ 0` and `ψ` with Lipschitz constant `|k|/8` in the frequency
coordinate, `{ξ ∈ D : |⟨k, ω'(ξ)⟩ + ψ(ξ)| < η}` is Borel of measure `≤ 8 η ρ_ζ / (|k| D_A)`.
-/

@[expose] public noncomputable section

open Real Finsupp MeasureTheory

namespace KAM.Wave

section

variable (m : ℝ) (hm : 0 < m)
variable {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {D : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ → ℝ} {εω ε1 ε2 θ : ℝ}

theorem omegaTan_injective : Function.Injective (omegaTan m hm) := by
  intro ξ ξ' h
  have := norm_sub_le_measLA_mul m hm ξ ξ'
  rw [h, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem continuous_omegaTan : Continuous (omegaTan m hm) :=
  (LipschitzWith.of_dist_le' (K := measNA m hm) (f := omegaTan m hm)
    (fun x y => measNA_dist_le m hm x y)).continuous

/-- The difference of the zone functions along a coordinate line is bounded below. -/
theorem IsFreqPair.zone_diff_bounds (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ)
    {k : Fin 2 → ℤ} (ψ : (Fin 2 → ℝ) → ℝ)
    (hψ : ∀ ξ ∈ D, ∀ ξ' ∈ D, |ψ ξ - ψ ξ'| ≤ kAbs k / 8 * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖)
    {ξ ξ' : Fin 2 → ℝ} (hξ : ξ ∈ D) (hξ' : ξ' ∈ D) :
    |(∑ i, (k i : ℝ) * ω ξ i + ψ ξ) - (∑ i, (k i : ℝ) * ω ξ' i + ψ ξ')| ≤
        (kAbs k * measNA m hm + θ * kAbs k + kAbs k / 8 * measNA m hm) * ‖ξ - ξ'‖ ∧
      ∀ i : Fin 2, (∀ j, j ≠ i → omegaTan m hm ξ j = omegaTan m hm ξ' j) →
        kAbs k / 2 ≤ |(k i : ℝ)| →
        kAbs k / 4 * |omegaTan m hm ξ i - omegaTan m hm ξ' i| ≤
          |(∑ i, (k i : ℝ) * ω ξ i + ψ ξ) - (∑ i, (k i : ℝ) * ω ξ' i + ψ ξ')| := by
  set d : Fin 2 → ℝ := omegaTan m hm ξ - omegaTan m hm ξ' with hd
  set e : Fin 2 → ℝ := (ω ξ - omegaTan m hm ξ) - (ω ξ' - omegaTan m hm ξ') with he
  have hθ0 := hP.θ_mem.1
  have hθLA := theta_mul_LA_le m hm hP.θ_mem.2
  have hLA := measLA_pos m hm
  have hk0 := kAbs_nonneg k
  have hen : ‖e‖ ≤ θ * ‖ξ - ξ'‖ := hP.h1_lip ξ hξ ξ' hξ'
  have hdn : ‖d‖ ≤ measNA m hm * ‖ξ - ξ'‖ := norm_omegaTan_sub_le m hm ξ ξ'
  have hΔ : ‖ξ - ξ'‖ ≤ measLA m hm * ‖d‖ := norm_sub_le_measLA_mul m hm ξ ξ'
  have hψd := hψ ξ hξ ξ' hξ'
  have hdecomp : (∑ i, (k i : ℝ) * ω ξ i + ψ ξ) - (∑ i, (k i : ℝ) * ω ξ' i + ψ ξ') =
      ∑ i, (k i : ℝ) * d i + ∑ i, (k i : ℝ) * e i + (ψ ξ - ψ ξ') := by
    simp only [hd, he, _root_.Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hkd := abs_sum_k_mul_le k d
  have hke := abs_sum_k_mul_le k e
  constructor
  · rw [hdecomp]
    have h1 : |∑ i, (k i : ℝ) * d i + ∑ i, (k i : ℝ) * e i + (ψ ξ - ψ ξ')| ≤
        |∑ i, (k i : ℝ) * d i| + |∑ i, (k i : ℝ) * e i| + |ψ ξ - ψ ξ'| := by
      refine (abs_add_le _ _).trans ?_
      gcongr
      exact abs_add_le _ _
    refine h1.trans ?_
    have n1 : ‖d‖ * kAbs k ≤ measNA m hm * ‖ξ - ξ'‖ * kAbs k :=
      mul_le_mul_of_nonneg_right hdn hk0
    have n2 : ‖e‖ * kAbs k ≤ θ * ‖ξ - ξ'‖ * kAbs k := mul_le_mul_of_nonneg_right hen hk0
    have n3 : kAbs k / 8 * ‖d‖ ≤ kAbs k / 8 * (measNA m hm * ‖ξ - ξ'‖) :=
      mul_le_mul_of_nonneg_left hdn (by positivity)
    nlinarith
  · intro i hi hki
    have hdi : ∀ j, j ≠ i → d j = 0 := fun j hj => by
      simp only [hd, _root_.Pi.sub_apply]; rw [hi j hj]; ring
    have hsum : ∑ j, (k j : ℝ) * d j = (k i : ℝ) * d i :=
      Finset.sum_eq_single i (fun j _ hj => by rw [hdi j hj, mul_zero]) (by simp)
    have hdnorm : ‖d‖ ≤ |d i| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · rw [hdi j hj]; simp
    have hdi' : d i = omegaTan m hm ξ i - omegaTan m hm ξ' i := by simp [hd]
    have hΔ' : ‖ξ - ξ'‖ ≤ measLA m hm * |d i| :=
      hΔ.trans (mul_le_mul_of_nonneg_left hdnorm hLA.le)
    have k1 : θ * ‖ξ - ξ'‖ ≤ 1 / 8 * |d i| := by
      calc θ * ‖ξ - ξ'‖ ≤ θ * (measLA m hm * |d i|) := mul_le_mul_of_nonneg_left hΔ' hθ0
        _ = (θ * measLA m hm) * |d i| := by ring
        _ ≤ 1 / 8 * |d i| := mul_le_mul_of_nonneg_right hθLA (abs_nonneg _)
    have hA : kAbs k / 2 * |d i| ≤ |(k i : ℝ) * d i| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hki (abs_nonneg _)
    have hB : |∑ j, (k j : ℝ) * e j + (ψ ξ - ψ ξ')| ≤ kAbs k / 4 * |d i| := by
      refine (abs_add_le _ _).trans ?_
      have b2 : ‖e‖ * kAbs k ≤ (1 / 8 * |d i|) * kAbs k :=
        mul_le_mul_of_nonneg_right (hen.trans k1) hk0
      have b3 : |ψ ξ - ψ ξ'| ≤ kAbs k / 8 * |d i| :=
        hψd.trans (mul_le_mul_of_nonneg_left hdnorm (by positivity))
      nlinarith
    have hAB := abs_sub_abs_le_abs_sub ((k i : ℝ) * d i)
      (-(∑ j, (k j : ℝ) * e j + (ψ ξ - ψ ξ')))
    rw [abs_neg, sub_neg_eq_add] at hAB
    rw [← hdi', hdecomp, hsum, add_assoc]
    nlinarith


/-- **Zone estimate** (blueprint `bpW:w7:zone`). -/
theorem IsFreqPair.zone_measure_le (hP : IsFreqPair m hm Pi α D ω Ω εω ε1 ε2 θ)
    {k : Fin 2 → ℤ} (hk : k ≠ 0) (ψ : (Fin 2 → ℝ) → ℝ)
    (hψ : ∀ ξ ∈ D, ∀ ξ' ∈ D, |ψ ξ - ψ ξ'| ≤ kAbs k / 8 * ‖omegaTan m hm ξ - omegaTan m hm ξ'‖)
    {ρζ : ℝ}
    (hρζ : ∀ ξ ∈ D, ∀ ξ' ∈ D, ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ ≤ ρζ) {η : ℝ} (hη : 0 < η) :
    MeasurableSet {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + ψ ξ| < η} ∧
      volume {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + ψ ξ| < η} ≤
        ENNReal.ofReal (8 * η * ρζ / (kAbs k * measDA m hm)) := by
  set F : (Fin 2 → ℝ) → ℝ := fun ξ => ∑ i, (k i : ℝ) * ω ξ i + ψ ξ with hF
  set S0 : Set (Fin 2 → ℝ) := {ξ ∈ D | |F ξ| < η} with hS0
  have hk1 := one_le_kAbs hk
  have hDA := measDA_pos m hm
  -- continuity of `F` on `D`
  have hcont : ContinuousOn F D := by
    set C := kAbs k * measNA m hm + θ * kAbs k + kAbs k / 8 * measNA m hm with hC
    have hlip := LipschitzOnWith.of_dist_le' (K := C) (f := F) (s := D) (fun x hx y hy => by
      rw [Real.dist_eq, dist_eq_norm]
      exact (hP.zone_diff_bounds m hm ψ hψ hx hy).1)
    exact hlip.continuousOn
  have hmeas : MeasurableSet S0 := measurableSet_abs_lt_of_continuousOn hP.meas hcont η
  refine ⟨hmeas, ?_⟩
  -- the image in the frequency coordinate
  set S : Set (Fin 2 → ℝ) := omegaTan m hm '' S0 with hS
  have hSmeas : MeasurableSet S :=
    hmeas.image_of_continuousOn_injOn (continuous_omegaTan m hm).continuousOn
      ((omegaTan_injective m hm).injOn)
  have hvol : volume S = ENNReal.ofReal (measDA m hm) * volume S0 :=
    measure_omegaTan_image m hm S0
  -- choose the coordinate
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, kAbs k / 2 ≤ |(k i : ℝ)| := by
    have : kAbs k = |(k 0 : ℝ)| + |(k 1 : ℝ)| := by simp [kAbs, Fin.sum_univ_two]
    rcases le_total |(k 1 : ℝ)| |(k 0 : ℝ)| with h | h
    · exact ⟨0, by linarith⟩
    · exact ⟨1, by linarith⟩
  set φ : (Fin 2 → ℝ) → ℝ := fun ζ => F (Function.invFun (omegaTan m hm) ζ) with hφ
  have hφ' : ∀ ξ, φ (omegaTan m hm ξ) = F ξ := fun ξ => by
    simp only [hφ]
    rw [Function.leftInverse_invFun (omegaTan_injective m hm)]
  have hslab := slab_measure_le i hSmeas (ρ := ρζ) (σ := kAbs k / 4) (η := η)
    (by positivity) hη.le φ
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [dist_eq_norm]
      exact hρζ x hx.1 y hy.1)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [hφ']
      exact hx.2)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      rw [hφ', hφ']
      exact (hP.zone_diff_bounds m hm ψ hψ hx.1 hy.1).2 i hxy hi)
  rw [hvol] at hslab
  have hpos : 0 < kAbs k := by linarith
  have hkey : ENNReal.ofReal (measDA m hm) * volume S0 ≤
      ENNReal.ofReal (measDA m hm) * ENNReal.ofReal (8 * η * ρζ / (kAbs k * measDA m hm)) := by
    rw [← ENNReal.ofReal_mul hDA.le]
    refine hslab.trans (le_of_eq ?_)
    congr 1
    field_simp
    ring
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hDA) ENNReal.ofReal_ne_top).1 hkey
    |> fun h => by simpa using h

end

end KAM.Wave

end
