/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Slab
public import KAM.Nekhoroshev.Averaging.Corrector
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part N12: dyadic shell integrals (`bpN:p12:shells`)

For `k ≠ 0` the integrals over `G` of `|ψ_κ(k·ω)|`, `|ψ'_κ(k·ω)|` and `κ²/((k·ω)²+κ²)` are bounded
using only the slab estimate `vol {I ∈ G | |k·ω(I)| ≤ u} ≤ C₁ u / |k|₂`.

* `shell_bound`: the integrand is pointwise dominated by a sum of indicators of the dyadic
  sublevel sets `|Q| ≤ κ 2^(j+1)` (`sh-shells`); the integral is bounded by the slab estimate
  (`sh-i`, `sh-ii`, `sh-iii`).
* `AvgShell.geom_shell_bound`: the geometric weights `A (2⁻ʲ)²` used by `ψ'` and the residual
  symbol sum to `5 A V κ`.
* `shells_from_slab`: the conditional helper (slab constant given); `shells` constructs it.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace KAM.Nekhoroshev

variable {n : ℕ} {R s : ℝ} {h : (Fin n → ℂ) → ℂ} {f : AvgComplexPhase n → ℂ}

namespace AvgShell

/-- The indicator of the sublevel set `|y| ≤ u` is measurable. -/
theorem measurable_sub (u : ℝ) (c : ℝ≥0∞) :
    Measurable ({y : ℝ | |y| ≤ u}.indicator (fun _ => c)) :=
  measurable_const.indicator (measurableSet_le continuous_abs.measurable measurable_const)

/-- Pointwise domination by dyadic sublevel indicators. -/
theorem pointwise {κ : ℝ} {g : ℝ → ℝ≥0∞} {c₀ : ℝ≥0∞} {a : ℕ → ℝ≥0∞}
    (hg0 : ∀ y, |y| ≤ κ → g y ≤ c₀)
    (hga : ∀ j : ℕ, ∀ y, κ * 2 ^ j < |y| → |y| ≤ κ * 2 ^ (j + 1) → g y ≤ a j)
    (y : ℝ) : ∀ N : ℕ, |y| ≤ κ * 2 ^ N →
      g y ≤ {y : ℝ | |y| ≤ κ}.indicator (fun _ => c₀) y +
        ∑ j ∈ Finset.range N, {y : ℝ | |y| ≤ κ * 2 ^ (j + 1)}.indicator (fun _ => a j) y := by
  intro N
  induction N with
  | zero =>
    intro hy
    have : |y| ≤ κ := by simpa using hy
    simp [Set.indicator_of_mem (show y ∈ {y : ℝ | |y| ≤ κ} from this), hg0 y this]
  | succ N ih =>
    intro hy
    by_cases hN : |y| ≤ κ * 2 ^ N
    · refine (ih hN).trans ?_
      rw [Finset.sum_range_succ, ← add_assoc]
      exact le_self_add
    · push Not at hN
      have h1 := hga N y hN hy
      have hmem : y ∈ {y : ℝ | |y| ≤ κ * 2 ^ (N + 1)} := hy
      rw [Finset.sum_range_succ, Set.indicator_of_mem hmem]
      exact h1.trans (le_add_self.trans le_add_self)

/-- The dyadic shell estimate: `∫ g (Q x) ≤ c₀ V κ + ∑_{j<N} aⱼ V κ 2^(j+1)`. -/
theorem shell_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q : α → ℝ}
    (hQ : AEMeasurable Q μ) {g : ℝ → ℝ≥0∞} {κ V : ℝ} (hV : 0 ≤ V)
    (hvol : ∀ u : ℝ, 0 < u → μ {x | |Q x| ≤ u} ≤ ENNReal.ofReal (V * u))
    {c : ℝ} (hc : 0 ≤ c) {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hκ : 0 < κ)
    (hg0 : ∀ y, |y| ≤ κ → g y ≤ ENNReal.ofReal c)
    (hga : ∀ j : ℕ, ∀ y, κ * 2 ^ j < |y| → |y| ≤ κ * 2 ^ (j + 1) →
      g y ≤ ENNReal.ofReal (a j))
    (N : ℕ) (hN : ∀ᵐ x ∂μ, |Q x| ≤ κ * 2 ^ N) :
    ∫⁻ x, g (Q x) ∂μ ≤
      ENNReal.ofReal (c * (V * κ) + ∑ j ∈ Finset.range N, a j * (V * (κ * 2 ^ (j + 1)))) := by
  have hmeas : ∀ (u : ℝ) (e : ℝ≥0∞), AEMeasurable
      (fun x => {y : ℝ | |y| ≤ u}.indicator (fun _ => e) (Q x)) μ :=
    fun u e => (measurable_sub u e).comp_aemeasurable hQ
  have hle : ∀ (u : ℝ) (e : ℝ≥0∞), 0 < u → ∫⁻ x, {y : ℝ | |y| ≤ u}.indicator (fun _ => e) (Q x) ∂μ ≤
      e * ENNReal.ofReal (V * u) := fun u e hu => by
    have : (fun x => {y : ℝ | |y| ≤ u}.indicator (fun _ => e) (Q x)) =
        {x | |Q x| ≤ u}.indicator (fun _ => e) := by
      funext x; simp [Set.indicator_apply]
    rw [this]
    exact (lintegral_indicator_const_le _ _).trans (mul_le_mul_right (hvol u hu) _)
  calc ∫⁻ x, g (Q x) ∂μ
      ≤ ∫⁻ x, ({y : ℝ | |y| ≤ κ}.indicator (fun _ => ENNReal.ofReal c) (Q x) +
          ∑ j ∈ Finset.range N, {y : ℝ | |y| ≤ κ * 2 ^ (j + 1)}.indicator
            (fun _ => ENNReal.ofReal (a j)) (Q x)) ∂μ :=
        lintegral_mono_ae (hN.mono fun x hx => pointwise hg0 hga (Q x) N hx)
    _ = ∫⁻ x, {y : ℝ | |y| ≤ κ}.indicator (fun _ => ENNReal.ofReal c) (Q x) ∂μ +
          ∑ j ∈ Finset.range N, ∫⁻ x, {y : ℝ | |y| ≤ κ * 2 ^ (j + 1)}.indicator
            (fun _ => ENNReal.ofReal (a j)) (Q x) ∂μ := by
        rw [lintegral_add_left' (hmeas _ _), lintegral_finsetSum' _ fun j _ => hmeas _ _]
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (V * κ) +
          ∑ j ∈ Finset.range N, ENNReal.ofReal (a j) *
            ENNReal.ofReal (V * (κ * 2 ^ (j + 1))) :=
        add_le_add (hle _ _ hκ) (Finset.sum_le_sum fun j _ => hle _ _ (by positivity))
    _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg hc (by positivity))
          (Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by positivity)),
          ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (ha j) (by positivity),
          ENNReal.ofReal_mul hc]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_mul (ha j)).symm

/-- Geometric weights `A (2⁻ʲ)²`: the shell integral is at most `5 A V κ`. -/
theorem geom_shell_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q : α → ℝ}
    (hQ : AEMeasurable Q μ) {g : ℝ → ℝ≥0∞} {κ V A : ℝ} (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hvol : ∀ u : ℝ, 0 < u → μ {x | |Q x| ≤ u} ≤ ENNReal.ofReal (V * u)) (hκ : 0 < κ)
    (hg0 : ∀ y, |y| ≤ κ → g y ≤ ENNReal.ofReal A)
    (hga : ∀ j : ℕ, ∀ y, κ * 2 ^ j < |y| → |y| ≤ κ * 2 ^ (j + 1) →
      g y ≤ ENNReal.ofReal (A * ((1 / 2 : ℝ) ^ j) ^ 2))
    (N : ℕ) (hN : ∀ᵐ x ∂μ, |Q x| ≤ κ * 2 ^ N) :
    ∫⁻ x, g (Q x) ∂μ ≤ ENNReal.ofReal (5 * (A * (V * κ))) := by
  refine (shell_bound hQ hV hvol hA (fun j => by positivity) hκ hg0 hga N hN).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hterm : ∀ j : ℕ, A * ((1 / 2 : ℝ) ^ j) ^ 2 * (V * (κ * 2 ^ (j + 1))) =
      2 * (A * (V * κ)) * (1 / 2 : ℝ) ^ j := fun j => by
    have : ((1 / 2 : ℝ) ^ j) * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    calc A * ((1 / 2 : ℝ) ^ j) ^ 2 * (V * (κ * 2 ^ (j + 1)))
        = 2 * (A * (V * κ)) * (1 / 2 : ℝ) ^ j * (((1 / 2 : ℝ) ^ j) * 2 ^ j) := by ring
      _ = _ := by rw [this, mul_one]
  simp only [hterm]
  rw [← Finset.mul_sum]
  have hg := sum_geometric_two_le N
  have h0 : 0 ≤ A * (V * κ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2 * (A * (V * κ)))]

/-! ### Facts about the mode `k` -/

theorem euclid_ge_one {k : Fin n → ℤ} (hk : k ≠ 0) : 1 ≤ euclid (fun j => (k j : ℝ)) := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk (funext hcon)
  have h1 : (1 : ℝ) ≤ (k j : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ k j ^ 2 := by nlinarith [sq_pos_of_ne_zero hj]
    exact_mod_cast this
  have h2 : (k j : ℝ) ^ 2 ≤ ∑ i, (k i : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => (k i : ℝ) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have h3 := AvgRank.euclid_sq (fun j => (k j : ℝ))
  have h4 : 0 ≤ euclid (fun j => (k j : ℝ)) := Real.sqrt_nonneg _
  nlinarith

theorem norm_le_euclid (k : Fin n → ℤ) : ‖fun j => (k j : ℝ)‖ ≤ euclid (fun j => (k j : ℝ)) := by
  have h4 : 0 ≤ euclid (fun j => (k j : ℝ)) := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg h4).2 fun j => ?_
  rw [Real.norm_eq_abs]
  have h2 : (k j : ℝ) ^ 2 ≤ ∑ i, (k i : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => (k i : ℝ) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have h3 := AvgRank.euclid_sq (fun j => (k j : ℝ))
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) h4 two_ne_zero).1 (by rw [sq_abs]; linarith)

theorem norm_le_mode (k : Fin n → ℤ) : ‖fun j => (k j : ℝ)‖ ≤ KAM.Fourier.modeSize k := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |(k i : ℝ)|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ j)

theorem mode_nonneg (k : Fin n → ℤ) : 0 ≤ KAM.Fourier.modeSize k :=
  Finset.sum_nonneg fun j _ => abs_nonneg _

theorem abs_Q_le {Ω₀ : ℝ} {I : Fin n → ℝ} (hI : ‖KAM.frequencyMap h I‖ ≤ Ω₀) (k : Fin n → ℤ) :
    |avgQ h k I| ≤ KAM.Fourier.modeSize k * Ω₀ := by
  unfold avgQ KAM.Fourier.modeSize
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    ((Real.norm_eq_abs _ ▸ norm_le_pi_norm (KAM.frequencyMap h I) j).trans hI) (abs_nonneg _)

theorem Q_aemeasurable (d : AveragingData n R s h f) (k : Fin n → ℤ) :
    AEMeasurable (avgQ h k) (volume.restrict (avgG n R)) := by
  have hfc : ContinuousOn (KAM.frequencyMap h) (avgG n R) :=
    (AvgRank.contDiffOn_freq d).continuousOn.mono (AvgRank.avgG_subset_domain d)
  refine ContinuousOn.aemeasurable ?_ measurableSet_closedBall
  unfold avgQ
  exact continuousOn_finsetSum _ fun j _ =>
    continuousOn_const.mul ((continuous_apply j).comp_continuousOn hfc)

theorem vol_restrict {C₁ : ℝ} (hC : AvgSlabBound h R C₁) {k : Fin n → ℤ} (hk : k ≠ 0) {u : ℝ}
    (hu : 0 < u) :
    volume.restrict (avgG n R) {x | |avgQ h k x| ≤ u} ≤
      ENNReal.ofReal (C₁ / euclid (fun j => (k j : ℝ)) * u) := by
  rw [Measure.restrict_apply' (show MeasurableSet (avgG n R) from measurableSet_closedBall)]
  have := hC.2 k hk u hu
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · congr 1; ext I; simp [and_comm]
  · congr 1; ring

theorem exists_N {Ω₀ κ : ℝ} (hκ : 0 < κ) (hΩ0 : 0 ≤ Ω₀) (k : Fin n → ℤ) :
    ∃ N : ℕ, KAM.Fourier.modeSize k * Ω₀ ≤ κ * 2 ^ N := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (KAM.Fourier.modeSize k * Ω₀ / κ) (one_lt_two (α := ℝ))
  refine ⟨N, ?_⟩
  rw [div_lt_iff₀ hκ] at hN
  linarith

theorem measurableSet_avgG : MeasurableSet (avgG n R) := measurableSet_closedBall

theorem ae_Q_le {Ω₀ κ : ℝ} {N : ℕ} {k : Fin n → ℤ}
    (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀)
    (hN : KAM.Fourier.modeSize k * Ω₀ ≤ κ * 2 ^ N) :
    ∀ᵐ I ∂(volume.restrict (avgG n R)), |avgQ h k I| ≤ κ * 2 ^ N :=
  (ae_restrict_iff' measurableSet_avgG).2
    (Filter.Eventually.of_forall fun I hI => (abs_Q_le (hΩ I hI) k).trans hN)

/-! ### The three integral estimates -/

theorem integral_psiD (d : AveragingData n R s h f) {C₁ Ω₀ κ : ℝ} (hC : AvgSlabBound h R C₁)
    (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) (hΩ0 : 0 ≤ Ω₀) (hκ : 0 < κ)
    {k : Fin n → ℤ} (hk : k ≠ 0) :
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsiD κ (avgQ h k I)|) ≤
      ENNReal.ofReal (5 * C₁ / (κ * euclid (fun j => (k j : ℝ)))) := by
  have hK := euclid_ge_one hk
  have hC1 := hC.1
  obtain ⟨N, hN⟩ := exists_N hκ hΩ0 k
  have hK0 : 0 < euclid (fun j => (k j : ℝ)) := by linarith
  refine (geom_shell_bound (Q_aemeasurable d k) (V := C₁ / euclid (fun j => (k j : ℝ)))
    (A := κ⁻¹ ^ 2) (g := fun y => ENNReal.ofReal |avgPsiD κ y|) (by positivity)
    (by positivity) (fun u hu => vol_restrict hC hk hu) hκ
    (fun y _ => ?_) (fun j y hy1 hy2 => ?_) N (ae_Q_le hΩ hN)).trans (le_of_eq ?_)
  · exact ENNReal.ofReal_le_ofReal ((corrector hκ).2 y).2.2.1
  · have hy0 : 0 < |y| := lt_of_le_of_lt (by positivity) hy1
    have hy : y ≠ 0 := abs_pos.1 hy0
    refine ENNReal.ofReal_le_ofReal ((((corrector hκ).2 y).2.2.2.2.2.2 hy).2.1.trans ?_)
    have h1 : |y|⁻¹ ≤ (κ * 2 ^ j)⁻¹ := inv_anti₀ (by positivity) hy1.le
    calc y⁻¹ ^ 2 = |y|⁻¹ ^ 2 := by rw [← sq_abs (y⁻¹), abs_inv]
      _ ≤ (κ * 2 ^ j)⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = _ := by rw [show ((1 / 2 : ℝ) ^ j) = (2 ^ j)⁻¹ by rw [one_div, inv_pow]]; field_simp
  · congr 1
    field_simp

theorem integral_resid (d : AveragingData n R s h f) {C₁ Ω₀ κ : ℝ} (hC : AvgSlabBound h R C₁)
    (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) (hΩ0 : 0 ≤ Ω₀) (hκ : 0 < κ)
    {k : Fin n → ℤ} (hk : k ≠ 0) :
    (∫⁻ I in avgG n R, ENNReal.ofReal (κ ^ 2 / (avgQ h k I ^ 2 + κ ^ 2))) ≤
      ENNReal.ofReal (5 * C₁ * κ / euclid (fun j => (k j : ℝ))) := by
  have hK := euclid_ge_one hk
  have hC1 := hC.1
  obtain ⟨N, hN⟩ := exists_N hκ hΩ0 k
  have hK0 : 0 < euclid (fun j => (k j : ℝ)) := by linarith
  refine (geom_shell_bound (Q_aemeasurable d k) (V := C₁ / euclid (fun j => (k j : ℝ)))
    (A := 1) (by positivity) (by positivity) (fun u hu => vol_restrict hC hk hu) hκ
    (g := fun y => ENNReal.ofReal (κ ^ 2 / (y ^ 2 + κ ^ 2)))
    (fun y _ => ?_) (fun j y hy1 hy2 => ?_) N (ae_Q_le hΩ hN)).trans (le_of_eq ?_)
  · exact ENNReal.ofReal_le_ofReal ((corrector hκ).2 y).2.2.2.2.2.1
  · have hy0 : 0 < |y| := lt_of_le_of_lt (by positivity) hy1
    have hy : y ≠ 0 := abs_pos.1 hy0
    refine ENNReal.ofReal_le_ofReal ((((corrector hκ).2 y).2.2.2.2.2.2 hy).2.2.trans ?_)
    have h1 : |y|⁻¹ ≤ (κ * 2 ^ j)⁻¹ := inv_anti₀ (by positivity) hy1.le
    calc κ ^ 2 * y⁻¹ ^ 2 = κ ^ 2 * |y|⁻¹ ^ 2 := by rw [← sq_abs (y⁻¹), abs_inv]
      _ ≤ κ ^ 2 * (κ * 2 ^ j)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 2) (by positivity)
      _ = 1 * ((1 / 2 : ℝ) ^ j) ^ 2 := by
          rw [show ((1 / 2 : ℝ) ^ j) = (2 ^ j)⁻¹ by rw [one_div, inv_pow]]; field_simp
  · congr 1
    field_simp

theorem integral_psi (d : AveragingData n R s h f) {C₁ Ω₀ κ : ℝ} (hC : AvgSlabBound h R C₁)
    (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) (hΩ0 : 0 ≤ Ω₀) (hκ : 0 < κ)
    {k : Fin n → ℤ} (hk : k ≠ 0) :
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (C₁ * (5 / 2 + 3 * max 0
        (Real.log (Ω₀ * KAM.Fourier.modeSize k / κ)))) := by
  have hK := euclid_ge_one hk
  have hC1 := hC.1
  set x : ℝ := Ω₀ * KAM.Fourier.modeSize k / κ with hx
  have hm := mode_nonneg (n := n) k
  have hx0 : 0 ≤ x := by positivity
  set t : ℝ := max 0 (Real.log x) with ht
  have ht0 : 0 ≤ t := le_max_left _ _
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  set N : ℕ := ⌈t / Real.log 2⌉₊ with hNdef
  have hxN : x ≤ 2 ^ N := by
    rcases hx0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have h1 : Real.log x ≤ N * Real.log 2 := by
        calc Real.log x ≤ t := le_max_right _ _
          _ ≤ (t / Real.log 2) * Real.log 2 := by rw [div_mul_cancel₀ _ hl2'.ne']
          _ ≤ N * Real.log 2 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl2'.le
      rw [← Real.log_le_log_iff hpos (by positivity), Real.log_pow]
      exact h1
  have hN : KAM.Fourier.modeSize k * Ω₀ ≤ κ * 2 ^ N := by
    have := (div_le_iff₀ hκ).1 (show Ω₀ * KAM.Fourier.modeSize k / κ ≤ 2 ^ N from hxN)
    linarith
  have hNle : (N : ℝ) ≤ 3 * t / 2 + 1 := by
    have h1 : (N : ℝ) < t / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : t / Real.log 2 ≤ 3 * t / 2 := by
      rw [div_le_iff₀ hl2']; nlinarith
    linarith
  have hK0 : 0 < euclid (fun j => (k j : ℝ)) := by linarith
  have hvol : ∀ u : ℝ, 0 < u →
      volume.restrict (avgG n R) {x | |avgQ h k x| ≤ u} ≤ ENNReal.ofReal (C₁ * u) :=
    fun u hu => (vol_restrict hC hk hu).trans (ENNReal.ofReal_le_ofReal (by
      have : C₁ / euclid (fun j => (k j : ℝ)) ≤ C₁ := div_le_self (by linarith) hK
      nlinarith))
  refine (shell_bound (Q_aemeasurable d k) (V := C₁)
    (g := fun y => ENNReal.ofReal |avgPsi κ y|) (by linarith) hvol
    (c := 1 / (2 * κ)) (a := fun j => 1 / (κ * 2 ^ j)) (by positivity) (fun j => by positivity)
    hκ (fun y _ => ?_) (fun j y hy1 hy2 => ?_) N (ae_Q_le hΩ hN)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · exact ENNReal.ofReal_le_ofReal ((corrector hκ).2 y).2.1
  · have hy0 : 0 < |y| := lt_of_le_of_lt (by positivity) hy1
    have hy : y ≠ 0 := abs_pos.1 hy0
    refine ENNReal.ofReal_le_ofReal ((((corrector hκ).2 y).2.2.2.2.2.2 hy).1.trans ?_)
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity) hy1.le
  · have hterm : ∀ j : ℕ, 1 / (κ * 2 ^ j) * (C₁ * (κ * 2 ^ (j + 1))) = 2 * C₁ := fun j => by
      field_simp; ring
    simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : 1 / (2 * κ) * (C₁ * κ) = C₁ / 2 := by field_simp
    rw [this]
    nlinarith

end AvgShell

/-- The logarithmic factor `1 + log (1/κ)`. -/
def avgLog (κ : ℝ) : ℝ := 1 + Real.log (1 / κ)

namespace AvgShell

theorem avgLog_nonneg {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) : 0 ≤ Real.log (1 / κ) :=
  Real.log_nonneg (by rw [le_div_iff₀ hκ]; linarith)

theorem log_le {P κ : ℝ} (hP : 0 ≤ P) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    max 0 (Real.log (P / κ)) ≤ P + Real.log (1 / κ) := by
  have hL := avgLog_nonneg hκ hκ1
  refine max_le (by linarith) ?_
  rcases hP.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hL
  · rw [div_eq_mul_one_div, Real.log_mul hpos.ne' (by positivity)]
    linarith [Real.log_le_sub_one_of_pos hpos]

end AvgShell

theorem shells_from_slab (d : AveragingData n R s h f) {C₁ Ω₀ κ : ℝ}
    (hC : AvgSlabBound h R C₁)
    (hΩ : ∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {k : Fin n → ℤ} (hk : k ≠ 0) :
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (C₁ * (5 / 2 + 3 * max 0 (Real.log (Ω₀ * KAM.Fourier.modeSize k / κ)))) ∧
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (3 * C₁ * (1 + Ω₀) * (1 + KAM.Fourier.modeSize k) * avgLog κ) ∧
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsiD κ (avgQ h k I)|) ≤
      ENNReal.ofReal (5 * C₁ / (κ * euclid (fun j => (k j : ℝ)))) ∧
    (∫⁻ I in avgG n R, ENNReal.ofReal (κ ^ 2 / (avgQ h k I ^ 2 + κ ^ 2))) ≤
      ENNReal.ofReal (5 * C₁ * κ / euclid (fun j => (k j : ℝ))) := by
  have hΩ0 : 0 ≤ Ω₀ := by
    have h0 : (0 : Fin n → ℝ) ∈ avgG n R := by
      simp only [avgG, mem_closedBall, dist_self]; linarith [d.hR]
    exact (norm_nonneg _).trans (hΩ 0 h0)
  have h1 := AvgShell.integral_psi d hC hΩ hΩ0 hκ hk
  refine ⟨h1, h1.trans (ENNReal.ofReal_le_ofReal ?_), AvgShell.integral_psiD d hC hΩ hΩ0 hκ hk,
    AvgShell.integral_resid d hC hΩ hΩ0 hκ hk⟩
  have hm := AvgShell.mode_nonneg (n := n) k
  have hC1 := hC.1
  have hL := AvgShell.avgLog_nonneg hκ hκ1
  have ht := AvgShell.log_le (mul_nonneg hΩ0 hm) hκ hκ1
  unfold avgLog
  have hP : 0 ≤ Ω₀ * KAM.Fourier.modeSize k := mul_nonneg hΩ0 hm
  have hprod : 0 ≤ Ω₀ * KAM.Fourier.modeSize k * Real.log (1 / κ) := mul_nonneg hP hL
  have hprod2 : 0 ≤ (Ω₀ + KAM.Fourier.modeSize k) * (1 + Real.log (1 / κ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hmain : 5 / 2 + 3 * max 0 (Real.log (Ω₀ * KAM.Fourier.modeSize k / κ)) ≤
      3 * (1 + Ω₀) * (1 + KAM.Fourier.modeSize k) * (1 + Real.log (1 / κ)) := by
    nlinarith
  calc C₁ * (5 / 2 + 3 * max 0 (Real.log (Ω₀ * KAM.Fourier.modeSize k / κ)))
      ≤ C₁ * (3 * (1 + Ω₀) * (1 + KAM.Fourier.modeSize k) * (1 + Real.log (1 / κ))) :=
        mul_le_mul_of_nonneg_left hmain (by linarith)
    _ = _ := by ring

/-- Source-facing node: the slab estimate is constructed, not assumed. -/
theorem shells (d : AveragingData n R s h f) :
    ∃ C₁ Ω₀ : ℝ, AvgSlabBound h R C₁ ∧ 0 ≤ Ω₀ ∧
      (∀ I ∈ avgG n R, ‖KAM.frequencyMap h I‖ ≤ Ω₀) ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ 1 → ∀ k : Fin n → ℤ, k ≠ 0 →
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (C₁ * (5 / 2 + 3 * max 0 (Real.log (Ω₀ * KAM.Fourier.modeSize k / κ)))) ∧
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsi κ (avgQ h k I)|) ≤
      ENNReal.ofReal (3 * C₁ * (1 + Ω₀) * (1 + KAM.Fourier.modeSize k) * avgLog κ) ∧
    (∫⁻ I in avgG n R, ENNReal.ofReal |avgPsiD κ (avgQ h k I)|) ≤
      ENNReal.ofReal (5 * C₁ / (κ * euclid (fun j => (k j : ℝ)))) ∧
    (∫⁻ I in avgG n R, ENNReal.ofReal (κ ^ 2 / (avgQ h k I ^ 2 + κ ^ 2))) ≤
      ENNReal.ofReal (5 * C₁ * κ / euclid (fun j => (k j : ℝ))) := by
  obtain ⟨C₁, hC⟩ := exists_avgSlabBound d
  obtain ⟨Ω₀, M₂, hΩ0, -, hΩ, -⟩ := avg_compact_bounds d
  have hG : avgG n R ⊆ closedBall (0 : Fin n → ℝ) R := fun I hI =>
    closedBall_subset_closedBall (by linarith [d.hR]) hI
  exact ⟨C₁, Ω₀, hC, hΩ0, fun I hI => hΩ I (hG hI), fun κ hκ hκ1 k hk =>
    shells_from_slab d hC (fun I hI => hΩ I (hG hI)) hκ hκ1 hk⟩

end KAM.Nekhoroshev

end
