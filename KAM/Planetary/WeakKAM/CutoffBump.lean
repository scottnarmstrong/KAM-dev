/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Data

/-! # P11B smooth cutoff: the one-variable bump

The exact polynomial bump `max (1 - x ^ 2) 0 ^ (μ + 1)`, its normalization by its exact positive
integral, and the facts used by the tensor cutoff: `C^μ` regularity, support in `[-1, 1]`,
positivity of the integral and finiteness of the `L¹` constants of the derivatives up to order `μ`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- Exact bump and integral constants of smooth-cutoff, not numerical quadrature. -/
def selectionBumpRaw (μ : ℕ) (x : ℝ) : ℝ := max (1 - x ^ 2) 0 ^ (μ + 1)
def selectionBump (μ : ℕ) (x : ℝ) : ℝ :=
  selectionBumpRaw μ x / ∫ y : ℝ, selectionBumpRaw μ y
def selectionBumpL1 (μ j : ℕ) : ℝ := ∫ y : ℝ, |iteratedDeriv j (selectionBump μ) y|
def selectionCutoffC (n μ k : ℕ) : ℝ := (n : ℝ) ^ k *
  sSup {v | ∃ a : Fin n → ℕ, (∑ i, a i) = k ∧ v = ∏ i, selectionBumpL1 μ (a i)}
def selectionExtensionC (n μ : ℕ) : ℝ := Real.sqrt n *
  sSup {v | ∃ k ≤ μ, v = (4 : ℝ) ^ k *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)}

theorem selectionPosPow_hasDerivAt (N : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ (N + 2)) (((N : ℝ) + 2) * max s 0 ^ (N + 1)) s := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have h : (fun s : ℝ => max s 0 ^ (N + 2)) =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with x hx
      simp [max_eq_right (le_of_lt (mem_Iio.1 hx)), pow_succ]
    have := (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq h
    simpa [max_eq_right hs.le, pow_succ] using this
  · subst hs
    simp only [max_self, zero_pow (Nat.succ_ne_zero _), mul_zero]
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min one_pos hc)] with h hh
    rw [Metric.mem_ball, dist_zero_right, lt_min_iff] at hh
    obtain ⟨h1, h2⟩ := hh
    have hm : max h 0 ≤ |h| := max_le (le_abs_self h) (abs_nonneg h)
    have hm0 : 0 ≤ max h 0 := le_max_right _ _
    have h3 : max h 0 ^ (N + 1) ≤ |h| ^ (N + 1) := pow_le_pow_left₀ hm0 hm _
    have h4 : |h| ^ (N + 1) ≤ |h| := pow_le_of_le_one (abs_nonneg h) h1.le (Nat.succ_ne_zero _)
    simp only [zero_add, smul_eq_mul, mul_zero, sub_zero, Real.norm_eq_abs, max_self,
      zero_pow (Nat.succ_ne_zero _)]
    rw [abs_of_nonneg (pow_nonneg hm0 _), pow_succ]
    calc max h 0 ^ (N + 1) * max h 0 ≤ |h| * |h| := by
          exact mul_le_mul (h3.trans h4) hm hm0 (abs_nonneg _)
      _ ≤ c * |h| := mul_le_mul_of_nonneg_right h2.le (abs_nonneg _)
  · have h : (fun s : ℝ => max s 0 ^ (N + 2)) =ᶠ[𝓝 s] fun x => x ^ (N + 2) := by
      filter_upwards [Ioi_mem_nhds hs] with x hx
      simp [max_eq_left (le_of_lt (mem_Ioi.1 hx))]
    have := (hasDerivAt_pow (N + 2) s).congr_of_eventuallyEq h
    simpa [max_eq_left hs.le] using this

theorem selectionPosPow_contDiff (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => max s 0 ^ (N + 1)) := by
  induction N with
  | zero =>
    have hc : Continuous fun s : ℝ => max s 0 ^ (0 + 1) := by fun_prop
    exact contDiff_zero.2 hc
  | succ N ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv (𝕜 := ℝ)]
    refine ⟨fun s => (selectionPosPow_hasDerivAt N s).differentiableAt, by simp, ?_⟩
    have : deriv (fun s : ℝ => max s 0 ^ (N + 1 + 1)) =
        fun s => ((N : ℝ) + 2) * max s 0 ^ (N + 1) :=
      funext fun s => (selectionPosPow_hasDerivAt N s).deriv
    rw [this]
    exact contDiff_const.mul ih

theorem selectionBumpRaw_contDiff (μ : ℕ) : ContDiff ℝ μ (selectionBumpRaw μ) :=
  (selectionPosPow_contDiff μ).comp (contDiff_const.sub (contDiff_id.pow 2))

theorem selectionBumpRaw_nonneg (μ : ℕ) (x : ℝ) : 0 ≤ selectionBumpRaw μ x :=
  pow_nonneg (le_max_right _ _) _

theorem selectionBumpRaw_eq_zero (μ : ℕ) {x : ℝ} (hx : 1 ≤ |x|) : selectionBumpRaw μ x = 0 := by
  have : 1 - x ^ 2 ≤ 0 := by
    have := (one_le_sq_iff_one_le_abs x).2 hx
    linarith
  simp [selectionBumpRaw, max_eq_right this]

theorem selectionBumpRaw_zero (μ : ℕ) : selectionBumpRaw μ 0 = 1 := by
  simp [selectionBumpRaw]

theorem selectionBumpRaw_support (μ : ℕ) : support (selectionBumpRaw μ) ⊆ Icc (-1) 1 := by
  intro x hx
  by_contra h
  refine hx (selectionBumpRaw_eq_zero μ ?_)
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem selectionBumpRaw_hasCompactSupport (μ : ℕ) : HasCompactSupport (selectionBumpRaw μ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (selectionBumpRaw_support μ)

theorem selectionBumpRaw_continuous (μ : ℕ) : Continuous (selectionBumpRaw μ) :=
  (selectionBumpRaw_contDiff μ).continuous

theorem selectionBumpInt_pos (μ : ℕ) : 0 < ∫ y : ℝ, selectionBumpRaw μ y :=
  (selectionBumpRaw_continuous μ).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (selectionBumpRaw_hasCompactSupport μ) (selectionBumpRaw_nonneg μ)
    (x := 0) (by rw [selectionBumpRaw_zero]; exact one_ne_zero)

theorem selectionBump_contDiff (μ : ℕ) : ContDiff ℝ μ (selectionBump μ) :=
  (selectionBumpRaw_contDiff μ).div_const _

theorem selectionBump_nonneg (μ : ℕ) (x : ℝ) : 0 ≤ selectionBump μ x :=
  div_nonneg (selectionBumpRaw_nonneg μ x) (selectionBumpInt_pos μ).le

theorem selectionBump_support (μ : ℕ) : support (selectionBump μ) ⊆ Icc (-1) 1 := by
  intro x hx
  refine selectionBumpRaw_support μ ?_
  intro h
  exact hx (by simp [selectionBump, h])

theorem selectionBump_hasCompactSupport (μ : ℕ) : HasCompactSupport (selectionBump μ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (selectionBump_support μ)

theorem selectionBump_integral (μ : ℕ) : ∫ y : ℝ, selectionBump μ y = 1 := by
  simp only [selectionBump]
  rw [integral_div, div_self (selectionBumpInt_pos μ).ne']

theorem selectionBump_iteratedDeriv_continuous {j : ℕ} (hj : j ≤ μ) :
    Continuous (iteratedDeriv j (selectionBump μ)) :=
  (selectionBump_contDiff μ).continuous_iteratedDeriv j (by exact_mod_cast hj)

theorem selectionBump_iteratedDeriv_hasCompactSupport (j : ℕ) :
    HasCompactSupport (iteratedDeriv j (selectionBump μ)) := by
  have h := (selectionBump_hasCompactSupport μ).iteratedFDeriv (𝕜 := ℝ) j
  have h2 := h.comp_left (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ) ℝ =>
    A (fun _ => 1)) rfl
  convert h2 using 1
  funext x
  simp [iteratedDeriv_eq_iteratedFDeriv]

theorem selectionBump_iteratedDeriv_integrable {j : ℕ} (hj : j ≤ μ) :
    Integrable (iteratedDeriv j (selectionBump μ)) :=
  (selectionBump_iteratedDeriv_continuous hj).integrable_of_hasCompactSupport
    (selectionBump_iteratedDeriv_hasCompactSupport j)

theorem selectionBumpL1_nonneg (μ j : ℕ) : 0 ≤ selectionBumpL1 μ j :=
  integral_nonneg fun _ => abs_nonneg _

end KAM.Planetary
