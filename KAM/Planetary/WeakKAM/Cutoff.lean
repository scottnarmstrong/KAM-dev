/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.CutoffConv

/-! # P11B smooth cutoff (`smooth-cutoff`)

The cutoff is the convolution of the indicator of the closed `t / 4`-neighbourhood of `E` with the
tensor kernel of width `t / 4`. The exact bump constants (`selectionBump`, `selectionBumpL1`,
`selectionCutoffC`, `selectionExtensionC`) live in `CutoffBump`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology Convolution
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionCutoffSet_bddAbove (n μ k : ℕ) :
    BddAbove {v | ∃ a : Fin n → ℕ, (∑ i, a i) = k ∧ v = ∏ i, selectionBumpL1 μ (a i)} := by
  refine Set.Finite.bddAbove (Set.Finite.subset
    ((Finset.finite_toSet (Fintype.piFinset fun _ : Fin n => Finset.range (k + 1))).image
      fun a => ∏ i, selectionBumpL1 μ (a i)) ?_)
  rintro v ⟨a, ha, rfl⟩
  refine ⟨a, ?_, rfl⟩
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  intro i
  have : a i ≤ ∑ i, a i := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem selectionMultilinear_expand {k : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ℝ) (a : Fin k → Fin n → ℝ) :
    F a = ∑ i : Fin k → Fin n, (∏ l, a l (i l)) * F (fun l => Pi.single (i l) 1) := by
  have ha : a = fun l => ∑ j ∈ (Finset.univ : Finset (Fin n)), a l j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    funext l j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [ha]
  rw [F.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.map_smul_univ]
  simp

theorem selectionKernel_integrable_deriv (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : k ≤ μ)
    (v : Fin k → Fin n → ℝ) :
    Integrable fun w => |iteratedFDeriv ℝ k (selectionKernel n μ δ) w v| := by
  have hc : Continuous fun w => |iteratedFDeriv ℝ k (selectionKernel n μ δ) w v| :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin n → ℝ) ℝ v).continuous.comp
      ((selectionKernel_contDiff n μ).continuous_iteratedFDeriv (by exact_mod_cast hk))).abs
  refine hc.integrable_of_hasCompactSupport ?_
  have h := (selectionKernel_hasCompactSupport n μ hδ).iteratedFDeriv (𝕜 := ℝ) k
  exact h.comp_left (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ℝ =>
    |A v|) (by simp)

theorem selectionKernel_deriv_bound (n μ : ℕ) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : k ≤ μ)
    (a : Fin k → Fin n → ℝ) (ha : ∀ l, ‖a l‖ ≤ 1) :
    ∫ w : Fin n → ℝ, |iteratedFDeriv ℝ k (selectionKernel n μ δ) w a| ≤
      selectionCutoffC n μ k * δ⁻¹ ^ k := by
  have hpt : ∀ w, |iteratedFDeriv ℝ k (selectionKernel n μ δ) w a| ≤
      ∑ i : Fin k → Fin n,
        |iteratedFDeriv ℝ k (selectionKernel n μ δ) w (fun l => Pi.single (i l) 1)| := by
    intro w
    rw [selectionMultilinear_expand]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have : |∏ l, a l (i l)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun l _ =>
        (le_trans (by simpa using norm_le_pi_norm (a l) (i l)) (ha l))
    exact mul_le_of_le_one_left (abs_nonneg _) this
  calc ∫ w : Fin n → ℝ, |iteratedFDeriv ℝ k (selectionKernel n μ δ) w a|
      ≤ ∫ w : Fin n → ℝ, ∑ i : Fin k → Fin n,
          |iteratedFDeriv ℝ k (selectionKernel n μ δ) w (fun l => Pi.single (i l) 1)| :=
        integral_mono (selectionKernel_integrable_deriv n μ hδ hk a)
          (integrable_finsetSum _ fun i _ => selectionKernel_integrable_deriv n μ hδ hk _) hpt
    _ = ∑ i : Fin k → Fin n, δ⁻¹ ^ k * ∏ j, selectionBumpL1 μ (selectionMult i j) := by
        rw [integral_finsetSum _ fun i _ => selectionKernel_integrable_deriv n μ hδ hk _]
        exact Finset.sum_congr rfl fun i _ => selectionKernel_coord_L1 n μ hδ hk i
    _ ≤ ∑ _i : Fin k → Fin n, δ⁻¹ ^ k *
          sSup {v | ∃ a : Fin n → ℕ, (∑ i, a i) = k ∧ v = ∏ i, selectionBumpL1 μ (a i)} := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_nonneg.2 hδ.le) _)
        exact le_csSup (selectionCutoffSet_bddAbove n μ k) ⟨selectionMult i, selectionMult_sum i, rfl⟩
    _ = selectionCutoffC n μ k * δ⁻¹ ^ k := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, selectionCutoffC]
        push_cast
        ring

theorem smooth_cutoff (hn : 1 ≤ n) (hμ : 1 ≤ μ) (E : Set (SelectionR n))
    (hE : IsCompact E) (hne : E.Nonempty) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ χ : SelectionR n → ℝ, ContDiff ℝ μ χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y ∈ E, χ y = 1) ∧
      tsupport χ ⊆ {y | Metric.infDist y E ≤ t / 2} ∧
      ∀ k ≤ μ, ∀ y, ∀ a : Fin k → SelectionR n, (∀ i, ‖a i‖ ≤ 1) →
        |iteratedFDeriv ℝ k χ y a| ≤ selectionCutoffC n μ k * (4 / t) ^ k := by
  set δ : ℝ := t / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set φ := selectionKernel n μ δ with hφ
  set A : Set (SelectionR n) := {z | Metric.infDist z E ≤ t / 4} with hA
  have hAc : IsClosed A := isClosed_le (Metric.continuous_infDist_pt E) continuous_const
  set u : SelectionR n → ℝ := A.indicator fun _ => 1 with hu
  have hul : LocallyIntegrable u := (locallyIntegrable_const (1 : ℝ)).indicator hAc.measurableSet
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have hφc : HasCompactSupport φ := selectionKernel_hasCompactSupport n μ hδ
  have hφi : Integrable φ := (selectionKernel_contDiff n μ).continuous.integrable_of_hasCompactSupport hφc
  have hconv : ∀ y, (u ⋆[L] φ) y = ∫ z, A.indicator (fun z => φ (y - z)) z := by
    intro y
    rw [convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ A <;> simp [hu, hL, hz]
  have hint : ∀ y, Integrable fun z => φ (y - z) := fun y => hφi.comp_sub_left y
  have hint1 : ∀ y, ∫ z, φ (y - z) = 1 := fun y => by
    rw [integral_sub_left_eq_self φ volume y, hφ, selectionKernel_integral n μ hδ]
  have hnn : ∀ w, 0 ≤ φ w := selectionKernel_nonneg n μ hδ
  refine ⟨u ⋆[L] φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hφc.contDiff_convolution_right L hul (by exact_mod_cast selectionKernel_contDiff n μ)
  · intro y
    rw [hconv, integral_indicator hAc.measurableSet]
    refine ⟨setIntegral_nonneg hAc.measurableSet fun z _ => hnn _, ?_⟩
    calc ∫ z in A, φ (y - z) ≤ ∫ z, φ (y - z) :=
          setIntegral_le_integral (hint y) (Eventually.of_forall fun z => hnn _)
      _ = 1 := hint1 y
  · intro y hy
    rw [hconv, integral_indicator hAc.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero, hint1]
    intro z hz
    by_contra hne0
    have hle := selectionKernel_ne_zero n μ hδ hne0
    apply hz
    show Metric.infDist z E ≤ t / 4
    calc Metric.infDist z E ≤ Metric.infDist y E + dist z y :=
          Metric.infDist_le_infDist_add_dist
      _ ≤ 0 + δ := by
          rw [Metric.infDist_zero_of_mem hy, dist_eq_norm, norm_sub_rev]
          exact add_le_add le_rfl hle
      _ = t / 4 := by rw [zero_add]
  · have hsupp : support (u ⋆[L] φ) ⊆ {y | Metric.infDist y E ≤ t / 2} := by
      intro y hy
      by_contra hyE
      apply hy
      rw [hconv]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
      simp only [Pi.zero_apply]
      by_cases hz : z ∈ A
      · rw [indicator_of_mem hz]
        by_contra hne0
        have hle := selectionKernel_ne_zero n μ hδ hne0
        apply hyE
        calc Metric.infDist y E ≤ Metric.infDist z E + dist y z :=
              Metric.infDist_le_infDist_add_dist
          _ ≤ t / 4 + δ := add_le_add hz (by rw [dist_eq_norm]; exact hle)
          _ = t / 2 := by rw [hδdef]; ring
      · rw [indicator_of_notMem hz]
    exact closure_minimal hsupp (isClosed_le (Metric.continuous_infDist_pt E) continuous_const)
  · intro k hk y a ha
    have hφk : ContDiff ℝ (k : ℕ) φ := (selectionKernel_contDiff n μ).of_le (by exact_mod_cast hk)
    rw [selectionConv_iteratedFDeriv hul k φ hφc hφk y a]
    have h4 : (4 / t) ^ k = δ⁻¹ ^ k := by rw [hδdef]; congr 1; field_simp
    rw [h4]
    refine le_trans (abs_integral_le_integral_abs) ?_
    calc ∫ z, |u z * iteratedFDeriv ℝ k φ (y - z) a|
        ≤ ∫ z, |iteratedFDeriv ℝ k φ (y - z) a| := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ?_
            (Eventually.of_forall fun z => ?_)
          · exact (selectionKernel_integrable_deriv n μ hδ hk a).comp_sub_left y
          · beta_reduce
            rw [abs_mul]
            refine mul_le_of_le_one_left (abs_nonneg _) ?_
            by_cases hz : z ∈ A <;> simp [hu, hz]
      _ = ∫ w, |iteratedFDeriv ℝ k φ w a| :=
          integral_sub_left_eq_self (fun w => |iteratedFDeriv ℝ k φ w a|) volume y
      _ ≤ _ := selectionKernel_deriv_bound n μ hδ hk a ha

end KAM.Planetary
