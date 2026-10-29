/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Extension
public import KAM.Planetary.WeakKAM.ExtensionStage
public import KAM.Planetary.WeakKAM.ExtensionNorm

/-! # GAP-P11a-SQ: the support step of `finite-extension` as a literal node export

`fe_supp` is `stepP:p11a:fe-supp`: a cutoff `χ_j` (`j < ν`) supported in
`{dist_∞(·, K_j) ≤ t_j/2}` has its support in `K + ϑ/(2√N)` (closed), hence at Euclidean distance
`≤ ϑ/2` from `K`, inside `K_ϑ ⊆ V`, and inside the real collar `K_j + t_j` of `B_j` with room.
Only the source premises are assumed (`t₀ ≤ ϑ/√N`, the support inclusion, the nested chain); the
inclusion `K_ϑ ⊆ V` is proved, not assumed.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- `stepP:p11a:fe-supp`: the supports of the cutoffs. -/
theorem fe_supp (d : SelectionData n) (a : SelectionSchedule n) (c : SelectionChain n) (ν : ℕ)
    (hc : SelectionExtensionChain d a c ν) (ht : 0 < a.t₀) (hτ : 0 ≤ a.τ)
    (htθ : a.t₀ ≤ d.ϑ / Real.sqrt n) {j : ℕ} (hj : j < ν) {χ : SelectionR n → ℝ}
    (hsupp : tsupport χ ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2}) :
    tsupport χ ⊆ {y | Metric.infDist y d.K ≤ d.ϑ / (2 * Real.sqrt n)} ∧
    tsupport χ ⊆ {y | ∃ x ∈ d.K, selectionLength (y - x) ≤ d.ϑ / 2} ∧
    {y | ∃ x ∈ d.K, selectionLength (y - x) ≤ d.ϑ / 2} ⊆ selectionThick d.K d.ϑ ∧
    selectionThick d.K d.ϑ ⊆ {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
    tsupport χ ⊆ selectionRealCollar (c.K j) (selectiont a j) := by
  have hn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast d.n_pos)
  have hKj : c.K j ⊆ d.K := by
    have := selectionChain_antitone hc (j := 0) j (by omega)
    simpa [hc.initial] using this
  have hne : (c.K j).Nonempty := hc.nonempty j hj.le
  have hcomp : IsCompact (c.K j) := hc.compact j hj.le
  have htj : selectiont a j ≤ a.t₀ := by
    unfold selectiont
    have : (2 : ℝ) ^ (-(a.τ + 1) * j) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
    calc a.t₀ * (2 : ℝ) ^ (-(a.τ + 1) * j) ≤ a.t₀ * 1 := mul_le_mul_of_nonneg_left this ht.le
      _ = a.t₀ := mul_one _
  have h1 : tsupport χ ⊆ {y | Metric.infDist y d.K ≤ d.ϑ / (2 * Real.sqrt n)} := by
    intro y hy
    have h := hsupp hy
    have hle : Metric.infDist y d.K ≤ Metric.infDist y (c.K j) :=
      Metric.infDist_le_infDist_of_subset hKj hne
    have : d.ϑ / (2 * Real.sqrt n) = d.ϑ / Real.sqrt n / 2 := by field_simp
    show Metric.infDist y d.K ≤ _
    rw [this]
    have : selectiont a j / 2 ≤ d.ϑ / Real.sqrt n / 2 := by
      have := htj.trans htθ
      linarith
    exact hle.trans (h.trans this)
  have h2 : tsupport χ ⊆ {y | ∃ x ∈ d.K, selectionLength (y - x) ≤ d.ϑ / 2} := by
    intro y hy
    have hy1 := h1 hy
    obtain ⟨x, hx, hd⟩ := d.compact.exists_infDist_eq_dist (hne.mono hKj) y
    refine ⟨x, hx, ?_⟩
    have hdist : ‖y - x‖ ≤ d.ϑ / (2 * Real.sqrt n) := by
      rw [← dist_eq_norm, ← hd]; exact hy1
    calc selectionLength (y - x) ≤ Real.sqrt n * ‖y - x‖ := selectionLength_le_sqrt_mul_norm _
      _ ≤ Real.sqrt n * (d.ϑ / (2 * Real.sqrt n)) := mul_le_mul_of_nonneg_left hdist hn.le
      _ = d.ϑ / 2 := by field_simp
  have h3 : {y | ∃ x ∈ d.K, selectionLength (y - x) ≤ d.ϑ / 2} ⊆ selectionThick d.K d.ϑ := by
    rintro y ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy.trans (by linarith [d.theta_pos])⟩
  have h4 : selectionThick d.K d.ϑ ⊆ {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} := by
    rintro y ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have e : (selectionReal y - fun i => (x i : ℂ)) = selectionReal (y - x) := by
      funext i; simp [selectionReal]
    rw [e, norm_selectionReal]
    exact lt_of_le_of_lt ((norm_le_selectionLength _).trans hxy) (by linarith [d.theta_pos])
  refine ⟨h1, h2, h3, h4, fun y hy => ?_⟩
  exact mem_selectionRealCollar_of_infDist hcomp hne
    (by linarith [selectiont_pos ht j]) (hsupp hy)

end KAM.Planetary

end
