/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.NormalForm.Taylor
public import KAM.Planetary.PlanarTorsion.NormalForm.Remainder
public import KAM.Planetary.PlanarTorsion.NormalForm.Bounds
public import KAM.Planetary.PlanarTorsion.QuarticFlow
public import KAM.Planetary.PlanarTorsion.Homological.Reality

/-!
# Planar quartic torsion: the Lie-series normal form estimate (package T10)

Blueprint P, Part 11b (`bpP:p11b:lie`, with `stepP:p11b:li-tay`, `stepP:p11b:li-ord`,
`stepP:p11b:li-sum`).  Composing `n₀ + F + R` with the time-one map of the homological solution
`χ` gives `n₀ + ⟨F⟩ + O (|z|⁶)`, uniformly on a compact parameter set:

* `li-tay`: `real_lie_taylor` (module `NormalForm/Taylor`) applied to `n₀` along the actual
  solution supplied by `flow`;
* `li-ord`: the brackets `{F, χ}` and `{{n₀, χ}, χ} = -{F - ⟨F⟩, χ}` have degree `4 + 4 - 2 = 6`
  (`NormalForm/Bounds`), and `R` has a vanishing five-jet (`NormalForm/Remainder`);
* `li-sum`: the cancellation `{n₀, χ} = -(F - ⟨F⟩)` from `ho_eq_reversed`.

The slow-independent `C` cancels.
-/

@[expose] public noncomputable section

open Set Metric Function MeasureTheory
open scoped Topology

namespace KAM.Planetary

open KAM KAM.ODE

/-- `p11c_flow` only depends on the Hamiltonian at the chosen parameter. -/
theorem p11cN_flow_congr {chi₁ chi₂ : (Fin 2 → ℝ) → Phase 2 → ℝ} {I : Fin 2 → ℝ}
    (h : chi₁ I = chi₂ I) : p11c_flow chi₁ I = p11c_flow chi₂ I := by
  unfold p11c_flow
  rw [h]

/-- The bracket with a quartic family is bounded by the product of cubic bounds. -/
theorem p11cN_bracket_le {G X : Phase 2 → ℝ} {c₁ c₂ : ℝ}
    (hG : ∀ w, ‖fderiv ℝ G w‖ ≤ c₁ * ‖w‖ ^ 3)
    (hX : ∀ w, ‖hamiltonianVectorField X w‖ ≤ c₂ * ‖w‖ ^ 3) (w : Phase 2) :
    |p11c_bracket G X w| ≤ c₁ * c₂ * ‖w‖ ^ 6 := by
  have h1 := (fderiv ℝ G w).le_opNorm (hamiltonianVectorField X w)
  have h2 : ‖fderiv ℝ G w‖ * ‖hamiltonianVectorField X w‖ ≤
      (c₁ * ‖w‖ ^ 3) * (c₂ * ‖w‖ ^ 3) :=
    mul_le_mul (hG w) (hX w) (norm_nonneg _) ((norm_nonneg _).trans (hG w))
  unfold p11c_bracket
  rw [← Real.norm_eq_abs]
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = c₁ * c₂ * ‖w‖ ^ 6 := by ring

/-- R has a vanishing 5-jet; no normal-form conclusion is an input. -/
theorem lie {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (F : QuarticFamily O)
    (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (hf : AnalyticOnNhd ℝ freq O) (hnr : p11c_NR4 O freq)
    (C : (Fin 2 → ℝ) → ℝ) (R : (Fin 2 → ℝ) × Phase 2 → ℝ)
    (hR : ∀ I ∈ O, AnalyticAt ℝ R (I, 0))
    (hj : ∀ I ∈ O, p11c_JetEq 5 (fun z => R (I, z)) 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
      |(C I + p11c_n0 freq I (p11c_flow (p11c_chi F freq) I 1 z) +
        F.eval I (p11c_flow (p11c_chi F freq) I 1 z) + R (I, p11c_flow (p11c_chi F freq) I 1 z)) -
        (C I + p11c_n0 freq I z + p11c_average F.eval I z)| ≤ A * (p11c_slowLength z) ^ 6 := by
  obtain ⟨⟨χ, hχ⟩, -⟩ := homological hO F freq hf hnr
  obtain ⟨Af, hAf⟩ := p11cN_average_family F
  obtain ⟨D, hD⟩ := p11cN_sub_family F Af
  obtain ⟨Cf, hCf, hgF⟩ := p11cN_grad_bound F hK hKO
  obtain ⟨CD, hCD, hgD⟩ := p11cN_grad_bound D hK hKO
  obtain ⟨Cx, hCx, hX⟩ := p11cQ_field_bound χ hK hKO
  obtain ⟨AR, rR, hrR, hRb⟩ := p11cN_remainder_bound R hR hj hK hKO
  obtain ⟨Cfl, r1, hCfl, hr1, -, hflow⟩ := flow hO χ K hK hKO
  refine ⟨8 * (Cf * Cx) + 8 * (CD * Cx) + 8 * |AR| + 1, min r1 (rR / 2), by positivity,
    lt_min hr1 (by linarith), ?_⟩
  intro I hI z hz
  have hIO : I ∈ O := hKO hI
  have hz1 : p11c_slowLength z < r1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : p11c_slowLength z < rR / 2 := lt_of_lt_of_le hz (min_le_right _ _)
  have hs0 : 0 ≤ p11c_slowLength z := Real.sqrt_nonneg _
  obtain ⟨h0, hsol, hen, -, -⟩ := hflow I hI z hz1
  have hfl : p11c_flow (p11c_chi F freq) I = p11c_flow χ.eval I :=
    (p11cN_flow_congr (hχ I hIO)).symm
  rw [hfl]
  set g : ℝ → Phase 2 := fun t => p11c_flow χ.eval I t z with hg
  have hg0 : g 0 = z := h0
  have hsol01 : IsSolutionIn (hamiltonianVectorField (χ.eval I)) univ (Icc (0 : ℝ) 1) g :=
    hsol.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hχa : AnalyticOnNhd ℝ (χ.eval I) univ := fun w _ => p11cQ_eval_slice_analytic χ hIO w
  have hFa : AnalyticOnNhd ℝ (F.eval I) univ := fun w _ => p11cQ_eval_slice_analytic F hIO w
  have hn0 : AnalyticOnNhd ℝ (p11c_n0 freq I) univ := by
    intro w _
    unfold p11c_n0 oscillatorAction
    have h1 : ∀ i, AnalyticAt ℝ (fun w : Phase 2 => w.1 i) w := fun i =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
        (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt w
    have h2 : ∀ i, AnalyticAt ℝ (fun w : Phase 2 => w.2 i) w := fun i =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
        (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt w
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      analyticAt_const.mul ((((h2 i).pow 2).add ((h1 i).pow 2)).div_const)
  have htay := real_lie_taylor isOpen_univ (p11c_n0 freq I) (χ.eval I) hn0 hχa g hsol01
  have hbr : p11c_bracket (p11c_n0 freq I) (χ.eval I) = fun w => -(D.eval I w) := by
    funext w
    rw [hχ I hIO, ho_eq_reversed F hnr hIO w, hD, hAf I hIO]
  rw [hbr] at htay
  have hfo := p11cN_first_order hFa hχa g hsol01
  -- pointwise bounds along the trajectory
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ ^ 6 ≤ 8 * p11c_slowLength z ^ 6 := by
    intro t ht
    have h1 := hen t ⟨by linarith [ht.1], ht.2⟩
    have h2 : ‖g t‖ ^ 2 ≤ 2 * p11c_slowLength z ^ 2 :=
      (p11cQ_norm_sq_le _).trans (by rw [← p11cQ_slowLength_sq]; exact h1)
    calc ‖g t‖ ^ 6 = (‖g t‖ ^ 2) ^ 3 := by ring
      _ ≤ (2 * p11c_slowLength z ^ 2) ^ 3 := by gcongr
      _ = 8 * p11c_slowLength z ^ 6 := by ring
  have hbF : ∀ w, |p11c_bracket (F.eval I) (χ.eval I) w| ≤ Cf * Cx * ‖w‖ ^ 6 :=
    p11cN_bracket_le (hgF I hI) (hX I hI)
  have hbD : ∀ w, |p11c_bracket (D.eval I) (χ.eval I) w| ≤ CD * Cx * ‖w‖ ^ 6 :=
    p11cN_bracket_le (hgD I hI) (hX I hI)
  have hJ1 : |∫ t in (0 : ℝ)..1, p11c_bracket (F.eval I) (χ.eval I) (g t)| ≤
      Cf * Cx * (8 * p11c_slowLength z ^ 6) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun t => p11c_bracket (F.eval I) (χ.eval I) (g t))
      (C := Cf * Cx * (8 * p11c_slowLength z ^ 6))
      (fun t ht => by
        have ht1 : 0 < t ∧ t ≤ 1 := by simpa [uIoc_of_le zero_le_one] using ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht1.1.le, ht1.2⟩
        rw [Real.norm_eq_abs]
        exact (hbF _).trans (by gcongr; exact hnorm t ht'))
    simpa using this
  have hJ2 : |∫ t in (0 : ℝ)..1, (1 - t) * -p11c_bracket (D.eval I) (χ.eval I) (g t)| ≤
      CD * Cx * (8 * p11c_slowLength z ^ 6) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun t => (1 - t) * -p11c_bracket (D.eval I) (χ.eval I) (g t))
      (C := CD * Cx * (8 * p11c_slowLength z ^ 6))
      (fun t ht => by
        have ht1 : 0 < t ∧ t ≤ 1 := by simpa [uIoc_of_le zero_le_one] using ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht1.1.le, ht1.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_neg]
        have h1 : |1 - t| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [ht'.1, ht'.2]
        calc |1 - t| * |p11c_bracket (D.eval I) (χ.eval I) (g t)|
            ≤ 1 * (CD * Cx * ‖g t‖ ^ 6) :=
              mul_le_mul h1 (hbD _) (abs_nonneg _) zero_le_one
          _ ≤ _ := by rw [one_mul]; gcongr; exact hnorm t ht')
    simpa using this
  have hRY : |R (I, g 1)| ≤ |AR| * (8 * p11c_slowLength z ^ 6) := by
    have h1 := hen 1 ⟨by norm_num, le_rfl⟩
    have h2 : ‖g 1‖ ^ 2 ≤ 2 * p11c_slowLength z ^ 2 :=
      (p11cQ_norm_sq_le _).trans (by rw [← p11cQ_slowLength_sq]; exact h1)
    have h3 : ‖g 1‖ ≤ rR := by
      by_contra hc
      push Not at hc
      nlinarith [norm_nonneg (g 1)]
    refine (hRb I hI (g 1) h3).trans ?_
    calc AR * ‖g 1‖ ^ 6 ≤ |AR| * ‖g 1‖ ^ 6 := by gcongr; exact le_abs_self _
      _ ≤ |AR| * (8 * p11c_slowLength z ^ 6) := by
        gcongr; exact hnorm 1 ⟨by norm_num, le_rfl⟩
  have hid : (C I + p11c_n0 freq I (g 1) + F.eval I (g 1) + R (I, g 1)) -
      (C I + p11c_n0 freq I z + p11c_average F.eval I z) =
      (∫ t in (0 : ℝ)..1, p11c_bracket (F.eval I) (χ.eval I) (g t)) +
      (∫ t in (0 : ℝ)..1, (1 - t) * -p11c_bracket (D.eval I) (χ.eval I) (g t)) +
      R (I, g 1) := by
    have hDz : D.eval I z = F.eval I z - p11c_average F.eval I z := by
      rw [hD, hAf I hIO]
    have h3 : (fun t => (1 - t) * p11c_bracket (fun w => -(D.eval I w)) (χ.eval I) (g t)) =
        fun t => (1 - t) * -p11c_bracket (D.eval I) (χ.eval I) (g t) := by
      funext t; rw [p11cN_bracket_neg]
    rw [h3, hg0] at htay
    rw [hg0] at hfo
    rw [htay, hfo]
    beta_reduce
    rw [hDz]
    ring
  rw [hid]
  refine (abs_add_three _ _ _).trans ?_
  nlinarith [hJ1, hJ2, hRY, pow_nonneg hs0 6, abs_nonneg AR]

end KAM.Planetary

end
