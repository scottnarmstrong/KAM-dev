/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.CompositionCoeff
public import KAM.Canonical.CompositionDomain
public import KAM.Canonical.Lie
public import KAM.Weighted.Parametric
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Lie series of the composition (`bpN:p5:composition` (ii), the engine)

Package C5-8. For `ComposeData` and `u ∈ O(r, s)` of norm `≤ U` write `a_j = ad_φ^j u / j!` and
`q = e η / 4` with `η = 2Φ/(ρσ) ≤ 1/2`.

* `KAM.Canonical.lieTerm_bound`: `a_j ∈ O(r-ρ, s-σ)` with `|a_j| ≤ q^j U` (`adjoint_bound`);
* `KAM.Canonical.lieSeries_class`, `lieSeries_bound`, `lieSeries_tail`: the sum `∑ a_j` is in the
  class with norm `≤ (1-q)⁻¹ U` and its tails are small in the norm;
* `KAM.Canonical.series_eq`: on `𝒟_{r-ρ, s-σ}` the series is `u ∘ X¹_φ` (`taylor_lie` with the
  hatted loss `ρ̂ = 3ρ/4`, `σ̂ = 3σ/4`, for which `η̂ ≤ 8/9`, so the Taylor remainder is
  `≤ q̂^N U`).
-/

@[expose] public noncomputable section

open Set Metric Filter Finset
open scoped Topology

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ U : ℝ}
  {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-! ### Numerics -/

private theorem exp_one_bounds : 0 < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 :=
  ⟨Real.exp_pos 1, Real.exp_one_lt_d9⟩

/-- `q = eη/4` for `0 ≤ η ≤ 1`: `0 ≤ q ≤ η` and `q < 1`. -/
theorem q_facts {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    0 ≤ Real.exp 1 * η / 4 ∧ Real.exp 1 * η / 4 ≤ η ∧ Real.exp 1 * η / 4 < 1 := by
  obtain ⟨he0, he1⟩ := exp_one_bounds
  refine ⟨by positivity, ?_, ?_⟩ <;> nlinarith

/-- The hatted ratio: `η̂ = 2Φ/(ρ̂σ̂) = 16η/9 ≤ 8/9` for `ρ̂ = 3ρ/4`, `σ̂ = 3σ/4`. -/
private theorem hat_eta {ρ σ Φ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) :
    2 * Φ / (ρ * (3 / 4) * (σ * (3 / 4))) = 16 / 9 * (2 * Φ / (ρ * σ)) := by
  field_simp
  ring

/-! ### The terms of the series -/

/-- `a_j ∈ O(r-ρ, s-σ)` with `|a_j| ≤ q^j U`. -/
theorem lieTerm_bound (hd : ComposeData D r s r' s' ρ σ Φ φ) (hu : InClass D r s u)
    (hb : WBound D r s u U) (j : ℕ) :
    InClass D (r - ρ) (s - σ) (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ∧
    WBound D (r - ρ) (s - σ) (fun z => ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      ((Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ j * U) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hcl : InClass D (r - ρ) (s - σ) u :=
      ⟨hu.differentiableOn.mono (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ])),
        fun j z hz => hu.periodic j z (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ]) hz)⟩
    have heq : EqOn u (fun z => (((0 : ℕ).factorial : ℂ)⁻¹) * adPow φ 0 u z)
        (Dom n D (r - ρ) (s - σ)) := fun z _ => by simp [adPow]
    refine ⟨inClass_congr heq hcl, wbound_congr (by linarith [hd.hσs]) heq ?_⟩
    simpa using hb.mono (by linarith [hd.hρ]) (by linarith [hd.hσ]) le_rfl
  · obtain ⟨h1, -, h3⟩ := adjoint_bound hd.φ_class hu hd.φ_bound hb hd.hρ hd.hρr hd.hσ hd.hσs
      (by linarith [hd.hr]) (by linarith [hd.hs]) hj
    exact ⟨inClass_const_mul _ h1, h3⟩

theorem ComposeData.eta_nonneg (hd : ComposeData D r s r' s' ρ σ Φ φ) : 0 ≤ 2 * Φ / (ρ * σ) :=
  div_nonneg (by linarith [hd.Φ_nonneg]) (mul_pos hd.hρ hd.hσ).le

/-- A negative bound is vacuous: `WBound` forces `0 ≤ U` as soon as some action is admitted. -/
theorem wbound_of_neg {r₀ r₁ s₀ s₁ M M' : ℝ} {v w : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hb : WBound D r₀ s₀ v M) (hM : M < 0) (hr : r₁ ≤ r₀) : WBound D r₁ s₁ w M' := by
  intro I hI
  obtain ⟨-, h2⟩ := hb I (polyNbhd_mono hr hI)
  have : 0 ≤ wsum v s₀ I :=
    tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  linarith

/-! ### The sum of the series -/

section Series

variable (hd : ComposeData D r s r' s' ρ σ Φ φ) (hu : InClass D r s u) (hb : WBound D r s u U)
include hd hu hb

omit hu hb in
theorem lieSeries_summable : Summable fun j : ℕ =>
    (Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ j * U := by
  obtain ⟨-, -, hq⟩ := q_facts (η := 2 * Φ / (ρ * σ)) hd.eta_nonneg (hd.eta_le.trans (by norm_num))
  have h0 : 0 ≤ Real.exp 1 * (2 * Φ / (ρ * σ)) / 4 := (q_facts (η := 2 * Φ / (ρ * σ))
    hd.eta_nonneg (hd.eta_le.trans (by norm_num))).1
  exact (summable_geometric_of_lt_one h0 hq).mul_right U

/-- The sum of the Lie series lies in the class `O(r-ρ, s-σ)`. -/
theorem lieSeries_class : InClass D (r - ρ) (s - σ)
    (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z) := by
  have hdom : (r - ρ) < r := by linarith [hd.hρ]
  have hterm := lieTerm_bound hd hu hb
  have hbd : ∀ j, ∀ z ∈ Dom n D (r - ρ) (s - σ),
      ‖((j.factorial : ℂ)⁻¹) * adPow φ j u z‖ ≤
        (Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ j * U := fun j =>
    sup_le_wbound (hterm j).1 (hterm j).2
  refine ⟨?_, fun j z hz => ?_⟩
  · refine (uniform_limit_holomorphic (isOpen_Dom _ _ _) (K := fun N z =>
      ∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      (fun N => ?_) (tendstoUniformlyOn_tsum_nat (lieSeries_summable hd) hbd)).1
    exact DifferentiableOn.fun_sum fun j _ => (hterm j).1.differentiableOn
  · exact tsum_congr fun i => by rw [(hterm i).1.periodic j z hz]

/-- `|∑ a_j|_{r-ρ,s-σ} ≤ (1-q)⁻¹ U`. -/
theorem lieSeries_bound : WBound D (r - ρ) (s - σ)
    (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
    ((1 - Real.exp 1 * (2 * Φ / (ρ * σ)) / 4)⁻¹ * U) := by
  have hterm := lieTerm_bound hd hu hb
  have h := wbound_tsum (by linarith [hd.hσs]) (fun j => (hterm j).1) (fun j => (hterm j).2)
    (lieSeries_summable hd)
  obtain ⟨h0, -, hq⟩ := q_facts (η := 2 * Φ / (ρ * σ))
    hd.eta_nonneg (hd.eta_le.trans (by norm_num))
  rwa [tsum_mul_right, tsum_geometric_of_lt_one h0 hq] at h

/-- The tails of the series are small in the weighted norm. -/
theorem lieSeries_tail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N, WBound D (r - ρ) (s - σ)
    (fun z => (∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z) -
      ∑ j ∈ range N', ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ε := by
  intro ε hε
  obtain ⟨h0, -, hq⟩ := q_facts (η := 2 * Φ / (ρ * σ))
    hd.eta_nonneg (hd.eta_le.trans (by norm_num))
  set q := Real.exp 1 * (2 * Φ / (ρ * σ)) / 4 with hqdef
  have hterm := lieTerm_bound hd hu hb
  have hlim : Tendsto (fun N : ℕ => q ^ N * ((1 - q)⁻¹ * U)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hq).mul_const ((1 - q)⁻¹ * U)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun N' hN' => ?_⟩
  have h := wbound_tsum (by linarith [hd.hσs]) (fun j => (hterm (j + N')).1)
    (fun j => (hterm (j + N')).2)
    ((summable_nat_add_iff N').2 (lieSeries_summable hd))
  have hsum : ∑' j : ℕ, q ^ (j + N') * U = q ^ N' * ((1 - q)⁻¹ * U) := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one h0 hq]
    ring
  rw [hsum] at h
  refine wbound_congr (by linarith [hd.hσs]) (fun z hz => ?_) (h.mono le_rfl le_rfl (hN N' hN').le)
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * adPow φ j u z :=
    Summable.of_norm_bounded (lieSeries_summable hd) fun j =>
      sup_le_wbound (hterm j).1 (hterm j).2 z hz
  rw [← hs'.sum_add_tsum_nat_add N', add_sub_cancel_left]

end Series

/-! ### Identification with `u ∘ X¹` -/

section Identify

variable (hd : ComposeData D r s r' s' ρ σ Φ φ) (hu : InClass D r s u) (hb : WBound D r s u U)
include hd hu hb

/-- On the trajectories from `𝒟_{r-ρ, s-σ}`, the iterates `ad_φ^N u / N!` are `≤ q̂^N U`, where
`q̂` is the constant of the loss `(3ρ/4, 3σ/4)`. -/
theorem adPow_traj_bound {N : ℕ} (hN : 1 ≤ N) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D (r - ρ) (s - σ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖adPow φ N u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)‖ ≤
      (N.factorial : ℝ) *
        ((Real.exp 1 * (2 * Φ / (ρ * (3 / 4) * (σ * (3 / 4)))) / 4) ^ N * U) := by
  have hρ' : 0 < ρ * (3 / 4) := by have := hd.hρ; positivity
  have hσ' : 0 < σ * (3 / 4) := by have := hd.hσ; positivity
  obtain ⟨h1, -, h3⟩ := adjoint_bound hd.φ_class hu hd.φ_bound hb hρ' (by linarith [hd.hρ, hd.hρr])
    hσ' (by linarith [hd.hσ, hd.hσs]) (by linarith [hd.hr, hd.hρ]) (by linarith [hd.hs, hd.hσ]) hN
  have hmem : flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z ∈
      Dom n D (r - ρ * (3 / 4)) (s - σ * (3 / 4)) := by
    have e1 : r - ρ * (3 / 4) = r - ρ + ρ * (1 / 4) := by ring
    have e2 : s - σ * (3 / 4) = s - σ + σ * (1 / 4) := by ring
    rw [e1, e2]
    exact hd.flow_mem_hat hz ⟨by linarith [ht.1], ht.2⟩
  have h4 := sup_le_wbound (inClass_const_mul ((N.factorial : ℂ)⁻¹) h1) h3 _ hmem
  have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.2 (Nat.factorial_pos N)
  calc _ = (N.factorial : ℝ) * ‖((N.factorial : ℂ)⁻¹) * adPow φ N u
          (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 hf.le

/-- On `𝒟_{r-ρ, s-σ}` the Lie series is `u ∘ X¹_φ`. -/
theorem series_eq {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) =
      ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z := by
  have hterm := lieTerm_bound hd hu hb
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * adPow φ j u z :=
    Summable.of_norm_bounded (lieSeries_summable hd) fun j =>
      sup_le_wbound (hterm j).1 (hterm j).2 z hz
  have hlim1 := hs'.hasSum.tendsto_sum_nat
  have hη := hd.eta_le
  have hη0 := hd.eta_nonneg
  have hhat : 2 * Φ / (ρ * (3 / 4) * (σ * (3 / 4))) = 16 / 9 * (2 * Φ / (ρ * σ)) :=
    hat_eta hd.hρ hd.hσ
  have hq := q_facts (η := 16 / 9 * (2 * Φ / (ρ * σ))) (by positivity) (by linarith)
  rw [← hhat] at hq
  obtain ⟨hq0, -, hq1⟩ := hq
  have hz1 : z ∈ gaugeInterior hd.gauge hd.omega (1 / 2) := hd.gaugeInterior_half hz
  have htaylor : ∀ N : ℕ, 1 ≤ N → ‖∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * adPow φ j u z -
      u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z)‖ ≤
      (Real.exp 1 * (2 * Φ / (ρ * (3 / 4) * (σ * (3 / 4)))) / 4) ^ N * U := fun N hN => by
    obtain ⟨h1, h2⟩ := taylor_lie (u := u) (hd.φ_class.differentiableOn.mono
      (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ]))) hd.smallField (isOpen_Dom _ _ _)
      (Dom_mono (by linarith [hd.hr]) (by linarith [hd.hs])) hu.differentiableOn hz1
      (fun t ht => (composition_domain hd).2.2.2 z hz t ht) hN
    have hB := h2 _ fun t ht => adPow_traj_bound hd hu hb hN hz ht
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.2 (Nat.factorial_pos N)
    have h1' : u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) = _ := h1
    rw [h1', sub_add_cancel_left, norm_neg]
    refine hB.trans_eq ?_
    field_simp
  have hlim2 : Tendsto (fun N : ℕ => ∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      atTop (𝓝 (u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop 1).mono fun N hN => htaylor N hN) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const U
  exact tendsto_nhds_unique hlim2 hlim1

end Identify

end KAM.Canonical

end
