/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Sublevel

/-!
# Measure of the small-divisor set (blueprint `bpP:p11a:diophantine-measure`, P11A-W7)

Compactness of the good set (`stepP:p11a:dm-compact`, `p11_dm_compact`), the union of sublevel sets
(`stepP:p11a:dm-union`, `p11_dm_union`), the sublevel estimate for one mode
(`stepP:p11a:dm-onek`, `p11_dm_onek`) and the countable-subadditivity sum
(`stepP:p11a:dm-sum`, in `diophantine_measure`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KAM.Planetary

section DioMeasure

variable {n m : ℕ}

theorem p11_K_sub_V (P : P11Patch n) : P.K ⊆ P.V := fun x hx =>
  P.thick_sub ⟨x, hx, by simp [p11euclid_zero, P.v_pos.le]⟩

theorem continuous_p11dotZ (k : Fin m → ℤ) : Continuous (p11dotZ k) := by
  unfold p11dotZ; fun_prop

/-- `stepP:p11a:dm-compact`. -/
theorem p11_dm_compact {P : P11Patch n} {mu : ℕ}
    {wt : (Fin m → ℤ) → P11Vec n → P11Vec m}
    (hwt : ∀ k, k ≠ 0 → ContDiffOn ℝ mu (wt k) P.V) (psi : (Fin m → ℤ) → ℝ) :
    IsCompact (p11Good P.K wt psi) := by
  have hKc := P.compact.isClosed
  have hclosed : IsClosed (p11Good P.K wt psi) := by
    have : p11Good P.K wt psi = ⋂ k : Fin m → ℤ,
        {y | y ∈ P.K ∧ (k ≠ 0 → psi k ≤ |p11dotZ k (wt k y)|)} := by
      ext y
      simp only [p11Good, mem_ofPred_eq, mem_iInter]
      exact ⟨fun ⟨hy, h⟩ k => ⟨hy, h k⟩, fun h => ⟨(h 0).1, fun k => (h k).2⟩⟩
    rw [this]
    refine isClosed_iInter fun k => ?_
    by_cases hk : k = 0
    · simpa [hk] using hKc
    · have h1 : ContinuousOn (wt k) P.K := (hwt k hk).continuousOn.mono (p11_K_sub_V P)
      have hc : ContinuousOn (fun y => |p11dotZ k (wt k y)|) P.K :=
        (continuous_abs.comp (continuous_p11dotZ k)).comp_continuousOn h1
      have := hc.preimage_isClosed_of_isClosed hKc (isClosed_Ici (a := psi k))
      simpa [hk, Set.preimage, Set.inter_def] using this
  exact P.compact.of_isClosed_subset hclosed (fun y hy => hy.1)

theorem p11euclid_int_pos {k : Fin m → ℤ} (hk : k ≠ 0) :
    0 < p11euclid (fun i => (k i : ℝ)) := by
  rcases (p11euclid_nonneg (fun i => (k i : ℝ))).lt_or_eq with h | h
  · exact h
  · exfalso
    have := p11euclid_eq_zero h.symm
    apply hk; funext i
    have := congrFun this i
    simpa using this

theorem p11euclid_unit_int {k : Fin m → ℤ} (hk : k ≠ 0) :
    p11euclid ((p11euclid (fun i => (k i : ℝ)))⁻¹ • (fun i => (k i : ℝ))) = 1 := by
  rw [p11euclid_smul, abs_of_pos (inv_pos.2 (p11euclid_int_pos hk))]
  exact inv_mul_cancel₀ (p11euclid_int_pos hk).ne'

theorem p11dot_unit_int (k : Fin m → ℤ) (v : P11Vec m) :
    p11dot ((p11euclid (fun i => (k i : ℝ)))⁻¹ • (fun i => (k i : ℝ))) v =
      (p11euclid (fun i => (k i : ℝ)))⁻¹ * p11dotZ k v := by
  simp [p11dot, p11dotZ, Finset.mul_sum, mul_assoc]

/-- `stepP:p11a:dm-onek`: the sublevel hypotheses at the unit direction of one mode. -/
theorem p11_dm_onek_hyp {P : P11Patch n} {rho mu : ℕ}
    {w : P11Vec n → P11Vec m} {wt : (Fin m → ℤ) → P11Vec n → P11Vec m} {beta M : ℝ}
    (H : P11DioHyp P rho mu w wt beta M) {k : Fin m → ℤ} (hk : k ≠ 0) :
    P11SublevelHyp P mu
      (fun y => p11dot ((p11euclid (fun i => (k i : ℝ)))⁻¹ • (fun i => (k i : ℝ))) (w y) ^ rho)
      (fun y => p11dot ((p11euclid (fun i => (k i : ℝ)))⁻¹ • (fun i => (k i : ℝ))) (wt k y) ^ rho)
      beta M := by
  set c := (p11euclid (fun i => (k i : ℝ)))⁻¹ • (fun i => (k i : ℝ)) with hcdef
  have hc : p11euclid c = 1 := p11euclid_unit_int hk
  have hreg : ContDiffOn ℝ ((mu + 1 : ℕ) : WithTop ℕ∞) w P.V := by exact_mod_cast H.regular
  exact
    { mu_pos := H.mu_pos
      beta_pos := H.beta_pos
      size_ge := H.size_ge
      g_smooth := by
        have := (contDiffOn_p11dot hreg c).pow rho
        exact_mod_cast this
      gt_smooth := (contDiffOn_p11dot (H.perturbed_regular k hk) c).pow rho
      finite_type := fun y hy => H.amount.trans (index_def_le rho mu w hc hy)
      size := fun j h1 h2 y hy => H.size c hc j h1 h2 y hy
      close := H.close k hk c hc }

theorem p11Csub_nonneg {P : P11Patch n} {mu : ℕ} {M beta : ℝ} (hb : 0 < beta) (hM : 0 ≤ M) :
    0 ≤ p11Csub n mu (Metric.diam P.K) P.v (M / beta) := by
  have h1 : 0 ≤ M / beta := by positivity
  have h2 : 0 ≤ Metric.diam P.K := Metric.diam_nonneg
  have h3 : 0 < P.v := P.v_pos
  unfold p11Csub
  positivity

/-- `bpP:p11a:diophantine-measure`; `stepP:p11a:dm-union` and `stepP:p11a:dm-sum` are inlined. -/
theorem diophantine_measure {n m rho mu : ℕ} {P : P11Patch n}
    {w : P11Vec n → P11Vec m} {wt : (Fin m → ℤ) → P11Vec n → P11Vec m}
    {beta M : ℝ} (H : P11DioHyp P rho mu w wt beta M)
    (psi : (Fin m → ℤ) → ℝ) (hp : ∀ k, k ≠ 0 → 0 < psi k)
    (hsmall : ∀ k, k ≠ 0 → (psi k / p11euclid (fun i => (k i : ℝ)))^rho < beta/4) :
    IsCompact (p11Good P.K wt psi) ∧
    volume (P.K \ p11Good P.K wt psi) ≤
      ENNReal.ofReal (p11Csub n mu (Metric.diam P.K) P.v (M/beta) * beta^(-((mu : ℝ)⁻¹))) *
        ∑' k : {k : Fin m → ℤ // k ≠ 0},
          ENNReal.ofReal ((psi k / p11euclid (fun i => ((k.val i) : ℝ)))^
            ((rho : ℝ)/mu)) := by
  refine ⟨p11_dm_compact H.perturbed_regular psi, ?_⟩
  have hβ := H.beta_pos
  have hM : 0 ≤ M := hβ.le.trans H.size_ge
  have hA : 0 ≤ p11Csub n mu (Metric.diam P.K) P.v (M/beta) := p11Csub_nonneg hβ hM
  have hAb : 0 ≤ p11Csub n mu (Metric.diam P.K) P.v (M/beta) * beta^(-((mu : ℝ)⁻¹)) :=
    mul_nonneg hA (Real.rpow_nonneg hβ.le _)
  -- x k := psi k / |k|
  let x : {k : Fin m → ℤ // k ≠ 0} → ℝ := fun k => psi k / p11euclid (fun i => ((k.val i) : ℝ))
  have hx : ∀ k, 0 < x k := fun k =>
    div_pos (hp k k.2) (p11euclid_int_pos k.2)
  let S : {k : Fin m → ℤ // k ≠ 0} → Set (P11Vec n) := fun k =>
    {y ∈ P.K | |p11dot ((p11euclid (fun i => (k.val i : ℝ)))⁻¹ • (fun i => (k.val i : ℝ)))
      (wt k.val y) ^ rho| ≤ (x k) ^ rho}
  have hsub : P.K \ p11Good P.K wt psi ⊆ ⋃ k, S k := by
    intro y ⟨hyK, hy⟩
    have : ∃ k, k ≠ 0 ∧ |p11dotZ k (wt k y)| < psi k := by
      by_contra hcon
      push Not at hcon
      exact hy ⟨hyK, hcon⟩
    obtain ⟨k, hk, hlt⟩ := this
    refine mem_iUnion.2 ⟨⟨k, hk⟩, hyK, ?_⟩
    have hkpos := p11euclid_int_pos hk
    rw [abs_pow, p11dot_unit_int, abs_mul, abs_of_pos (inv_pos.2 hkpos)]
    refine pow_le_pow_left₀ (by positivity) ?_ rho
    have : (p11euclid (fun i => (k i : ℝ)))⁻¹ * |p11dotZ k (wt k y)| ≤
        (p11euclid (fun i => (k i : ℝ)))⁻¹ * psi k :=
      mul_le_mul_of_nonneg_left hlt.le (inv_pos.2 hkpos).le
    simpa [x, div_eq_inv_mul] using this
  have hterm : ∀ k, volume (S k) ≤
      ENNReal.ofReal (p11Csub n mu (Metric.diam P.K) P.v (M/beta) * beta^(-((mu : ℝ)⁻¹))) *
        ENNReal.ofReal ((x k) ^ ((rho : ℝ)/mu)) := by
    intro k
    have h1 := sublevel (eps := (x k) ^ rho) (p11_dm_onek_hyp H k.2) (pow_pos (hx k) rho)
      (hsmall k.1 k.2)
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hAb]
    congr 1
    have hxr : 0 ≤ x k ^ rho := (pow_pos (hx k) rho).le
    rw [Real.div_rpow hxr hβ.le, Real.rpow_neg hβ.le, ← Real.rpow_natCast,
      ← Real.rpow_mul (hx k).le, div_eq_mul_inv ((rho : ℝ)) (mu : ℝ), div_eq_mul_inv]
    ring
  calc volume (P.K \ p11Good P.K wt psi) ≤ volume (⋃ k, S k) := measure_mono hsub
    _ ≤ ∑' k, volume (S k) := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal (p11Csub n mu (Metric.diam P.K) P.v (M/beta) *
          beta^(-((mu : ℝ)⁻¹))) * ENNReal.ofReal ((x k) ^ ((rho : ℝ)/mu)) :=
        ENNReal.tsum_le_tsum hterm
    _ = _ := ENNReal.tsum_mul_left

end DioMeasure

end KAM.Planetary
