/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.RealDynamics

/-!
# Two-scale KAM: passing the field to the limit (`stepP:p3:inv-lim`)

`curve_limit_field`: if differentiable real curves `x_j` converge uniformly to a continuous curve
`y` with values in an open set `U` on which the field `X` is continuous, and
`‖x_j' − X(x_j)‖ → 0` uniformly in `t`, then `y' = X(y)`. The field is compared at nearby points
through uniform continuity on a compact `δ`-thickening of the range of `y` over a compact time set
(the "common inner domain for close pairs" of design finding N2, not global uniform continuity).
Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

open KAM.Canonical

/-- The limit of differentiable curves whose derivatives asymptotically follow a field `X` that is
continuous on an open set containing the limit curve. -/
theorem curve_limit_field {n : ℕ} {X : Phase n → Phase n} {U : Set (Phase n)} (hU : IsOpen U)
    (hX : ContinuousOn X U) {x : ℕ → ℝ → Phase n} {y : ℝ → Phase n}
    (hx : ∀ j, Differentiable ℝ (x j)) (hy : Continuous y) (hyU : ∀ t, y t ∈ U)
    (hconv : TendstoUniformly x y atTop) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hder : ∀ j t, ‖deriv (x j) t - X (x j t)‖ ≤ ε j) :
    ∀ t, HasDerivAt y (X (y t)) t := by
  have hv : Continuous fun t => X (y t) :=
    hX.comp_continuous hy hyU
  refine real_curve_limit hx hconv.tendstoLocallyUniformly ?_ hv
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have hC : IsCompact (y '' K) := hK.image hy
  obtain ⟨δ, hδ, hsub⟩ := hC.exists_cthickening_subset_open hU (fun _ ⟨t, _, ht⟩ => ht ▸ hyU t)
  have hT : IsCompact (cthickening δ (y '' K)) := hC.cthickening
  have hUC : UniformContinuousOn X (cthickening δ (y '' K)) :=
    hT.uniformContinuousOn_of_continuous (hX.mono hsub)
  have hF : TendstoUniformlyOn (fun j t => X (x j t)) (fun t => X (y t)) atTop K := by
    refine UniformContinuousOn.comp_tendstoUniformlyOn_eventually ?_ ?_ hUC
      (hconv.tendstoUniformlyOn)
    · filter_upwards [(Metric.tendstoUniformly_iff.1 hconv) δ hδ] with j hj t ht
      exact mem_cthickening_of_dist_le _ _ δ _ ⟨t, ht, rfl⟩ (by rw [dist_comm]; exact (hj t).le)
    · exact fun t ht => self_subset_cthickening _ ⟨t, ht, rfl⟩
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro e he
  have hε' : ∀ᶠ j in atTop, ε j < e / 2 := (hε.eventually (gt_mem_nhds (by linarith)))
  filter_upwards [hF (e / 2) (by linarith), hε'] with j hj hj2 t ht
  have h1 := hj t ht
  have h2 := hder j t
  rw [dist_eq_norm] at h1 ⊢
  calc ‖X (y t) - deriv (x j) t‖
      ≤ ‖X (y t) - X (x j t)‖ + ‖X (x j t) - deriv (x j) t‖ := by
        have := norm_add_le (X (y t) - X (x j t)) (X (x j t) - deriv (x j) t)
        simpa using this
    _ < e := by rw [norm_sub_rev (X (x j t))]; linarith

end KAM.Planetary

end
