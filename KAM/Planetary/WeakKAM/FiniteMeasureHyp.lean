/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.FiniteMeasureBridge

/-! # P11B finite measure: the hypotheses `D1`-`D3` of the Diophantine measure estimate

`selectionM₀_bddAbove` and `selection_jet_le_M₀` make `selectionM₀` a genuine bound of the jets
of the frequency map; `selection_eta_le` is the `η_ρ(θ_max) ≤ β/2` step of `stepP:p11a:fm-close`;
`selectionDioHyp` assembles `P11DioHyp` for a family of smooth maps `θ_max`-close to `ω`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology Pointwise
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ}

theorem selectionFrequency_contDiffOn (d : SelectionData n) (m : ℕ) :
    ContDiffOn ℝ m (frequencyMap d.h) (selectionV d) :=
  selectionFrequencyMap_contDiffOn (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo m

theorem selectionDGVector_le_sqrt_mul_norm (hn : 1 ≤ n) (f : SelectionR n → SelectionR n)
    (j : ℕ) (y : SelectionR n) :
    selectionDGVector j f y ≤ Real.sqrt n * ‖iteratedFDeriv ℝ j f y‖ := by
  have hne : {v | ∃ a : SelectionR n, selectionLength a = 1 ∧
      v = selectionLength (iteratedFDeriv ℝ j f y (fun _ => a))}.Nonempty :=
    ⟨_, _, selectionLength_single_zero hn, rfl⟩
  unfold selectionDGVector
  refine csSup_le hne ?_
  rintro v ⟨a, ha, rfl⟩
  refine (selectionLength_le_sqrt_mul_norm _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ _i : Fin j, ‖a‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      fun _ _ => norm_le_one_of_selectionLength_eq_one ha
  exact mul_le_of_le_one_right (norm_nonneg _) this

theorem selectionM₀_bddAbove (d : SelectionData n) :
    BddAbove {v | ∃ j ≤ d.μ, ∃ y ∈ selectionThick d.K d.ϑ,
      v = selectionDGVector j (frequencyMap d.h) y} := by
  have hc := isCompact_selectionThick d.K d.compact d.ϑ
  have hB : ∀ j, ∃ B : ℝ, j ≤ d.μ → ∀ y ∈ selectionThick d.K d.ϑ,
      ‖iteratedFDeriv ℝ j (frequencyMap d.h) y‖ ≤ B := by
    intro j
    by_cases hj : j ≤ d.μ
    · have hsm := selectionFrequency_contDiffOn d d.μ
      have h1 := (hsm.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
        (isOpen_selectionV d).uniqueDiffOn)
      have h2 : ContinuousOn (iteratedFDeriv ℝ j (frequencyMap d.h)) (selectionV d) :=
        h1.congr (iteratedFDerivWithin_of_isOpen j (isOpen_selectionV d)).symm
      obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn
        (h2.mono (selectionThick_subset_V d)).norm
      exact ⟨B, fun _ y hy => by simpa using hB y hy⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose B hB using hB
  refine ⟨Real.sqrt n * ∑ j ∈ Finset.range (d.μ + 1), |B j|, ?_⟩
  rintro v ⟨j, hj, y, hy, rfl⟩
  refine (selectionDGVector_le_sqrt_mul_norm d.n_pos _ j y).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (hB j hj y hy).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem selection_jet_le_M₀ (d : SelectionData n) {j : ℕ} (hj : j ≤ d.μ) {y : SelectionR n}
    (hy : y ∈ selectionThick d.K d.ϑ) :
    selectionDGVector j (frequencyMap d.h) y ≤ selectionM₀ d :=
  le_csSup (selectionM₀_bddAbove d) ⟨j, hj, y, hy, rfl⟩

theorem selection_eta_le (d : SelectionData n) :
    p11eta d.ρ d.μ (selectionM₀ d) (selectionThetaMax d) ≤ d.β / 2 := by
  have hβ := d.beta_pos
  have hM := selectionM₀_nonneg d
  unfold p11eta selectionThetaMax
  by_cases h1 : d.ρ = 1
  · simp [h1]
  · simp only [h1, ite_false]
    set X : ℝ := 2 * selectionM₀ d + d.β with hX
    have hXp : 0 < X := by positivity
    have hp : (0 : ℝ) < 2 ^ (d.μ + 1) := by positivity
    set Θ : ℝ := min d.β (d.β / (2 ^ (d.μ + 1) * X)) with hΘ
    have hΘ1 : Θ ≤ d.β := min_le_left _ _
    have hΘ2 : Θ ≤ d.β / (2 ^ (d.μ + 1) * X) := min_le_right _ _
    have hΘ0 : 0 ≤ Θ := le_min hβ.le (by positivity)
    calc (2 : ℝ) ^ d.μ * Θ * (2 * selectionM₀ d + Θ) ≤ 2 ^ d.μ * Θ * X := by
          gcongr; linarith
      _ ≤ 2 ^ d.μ * (d.β / (2 ^ (d.μ + 1) * X)) * X := by gcongr
      _ = d.β / 2 := by
          rw [pow_succ]; field_simp

/-- `D1`-`D3` for a family of smooth maps staying `θ_max`-close to the frequency map. -/
theorem selectionDioHyp (d : SelectionData n) (wt : (Fin n → ℤ) → SelectionR n → SelectionR n)
    (hreg : ∀ k, k ≠ 0 → ContDiffOn ℝ d.μ (wt k) (selectionV d))
    (hclose : ∀ k, k ≠ 0 → ∀ j ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
      selectionDGVector j (wt k - frequencyMap d.h) y ≤ selectionThetaMax d) :
    P11DioHyp (selectionPatch d) d.ρ d.μ (frequencyMap d.h) wt d.β d.M := by
  have hV := isOpen_selectionV d
  have hw : ContDiffOn ℝ d.μ (frequencyMap d.h) (selectionV d) :=
    selectionFrequency_contDiffOn d d.μ
  have hat : ∀ {g : SelectionR n → ℝ} {m : ℕ}, ContDiffOn ℝ m g (selectionV d) →
      ∀ {j : ℕ}, j ≤ m → ∀ y ∈ selectionV d, ContDiffAt ℝ j g y :=
    fun hg j hj y hy => (hg.of_le (by exact_mod_cast hj)).contDiffAt (hV.mem_nhds hy)
  have hthick : ∀ y ∈ p11thick d.K d.ϑ, y ∈ selectionV d := fun y hy =>
    selectionThick_subset_V d (by rwa [selectionThick_eq_p11thick])
  refine ⟨d.n_pos, d.μ_pos, d.rho_mem, d.beta_pos, d.beta_le, ?_, hreg, ?_, ?_, ?_⟩
  · have := selectionFrequency_contDiffOn d (d.μ + 1)
    exact_mod_cast this
  · refine le_index_def d.n_pos d.ρ d.μ _ (selectionPatch d).nonempty fun c hc y hy => ?_
    have hcl : selectionLength c = 1 := by rw [selectionLength_eq_p11euclid]; exact hc
    obtain ⟨j, hj, hjb⟩ := d.finite_type c hcl y hy
    have hsc : ContDiffOn ℝ d.μ (selectionScalar d.ρ (frequencyMap d.h) c) (selectionV d) :=
      (contDiffOn_p11dot hw c).pow d.ρ
    have hg := hat hsc hj y (selectionThick_subset_V d
      (K_subset_selectionThick d.K d.theta_pos.le hy))
    refine hjb.trans ?_
    rw [← p11dg_scalar_eq_selectionDG _ hg]
    exact le_p11maxJet _ _ d.μ hj
  · intro c hc j hj1 hj2 y hy
    have hcl : selectionLength c = 1 := by rw [selectionLength_eq_p11euclid]; exact hc
    have hsc : ContDiffOn ℝ (d.μ + 1) (selectionScalar d.ρ (frequencyMap d.h) c) (selectionV d) :=
      by
        have := selectionFrequency_contDiffOn d (d.μ + 1)
        exact (contDiffOn_p11dot (by exact_mod_cast this) c).pow d.ρ
    have hg := hat hsc hj2 y (hthick y hy)
    unfold p11op
    refine Real.sSup_le ?_ (by linarith [d.beta_pos, d.beta_le])
    rintro v ⟨a, ha, rfl⟩
    have e := p11euclid_iteratedFDeriv_scalar hg a
    refine e.le.trans (d.top_bounds c hcl j hj1 hj2 y (by rwa [selectionThick_eq_p11thick]) a
      fun i => by rw [selectionLength_eq_p11euclid]; exact ha i)
  · intro k hk c hc
    have hb : p11JetBound true d.μ (p11thick d.K d.ϑ) (frequencyMap d.h) (selectionM₀ d) := by
      intro j hj y hy
      show p11dg _ j y ≤ _
      rw [p11dg_eq_selectionDGVector]
      exact selection_jet_le_M₀ d hj (by rwa [selectionThick_eq_p11thick])
    have he : p11JetBound true d.μ (p11thick d.K d.ϑ) (wt k - frequencyMap d.h)
        (selectionThetaMax d) := by
      intro j hj y hy
      show p11dg _ j y ≤ _
      rw [p11dg_eq_selectionDGVector]
      exact hclose k hk j hj y (by rwa [selectionThick_eq_p11thick])
    have := stability_jet hV hthick d.rho_mem hw (hreg k hk) (selectionM₀_nonneg d)
      (selectionThetaMax_pos d).le hb he hc
    intro j hj y hy
    exact (this j hj y hy).trans (selection_eta_le d)

end KAM.Planetary
