/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Patch

/-!
# Planar assembly: the action box inside the image of the good patch (Part 12)

Blueprint P, Part 12 (`bpP:p12:data`).  The componentwise monotone action map
`a ↦ m_i √(κ a_i)` maps the axis cube `closedBall a0 r` onto a box of actions.  For a cube with
`r < a0 i` the closed action box `∏ [lo_i, hi_i]` with `lo = actions (a0 - r)`,
`hi = actions (a0 + r)` is contained in the image of the cube.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM KAM.Kepler

theorem p12c_actions_sq (p : PlanarData) (hp : p.Valid) (b : Fin 2 → ℝ) (i : Fin 2)
    (hb : 0 ≤ b i) : p.actions b i ^ 2 = p.m i ^ 2 * p.kappa * b i := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  unfold PlanarData.actions
  rw [mul_pow, sq_sqrt (by positivity)]
  ring

theorem p12c_actions_nonneg (p : PlanarData) (hp : p.Valid) (b : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ p.actions b i := by
  have := hp.2.2 i
  unfold PlanarData.actions
  positivity

theorem p12c_box (p : PlanarData) (hp : p.Valid) (a0 : Fin 2 → ℝ) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ i, r < a0 i) :
    ∃ lo hi : Fin 2 → ℝ, (∀ i, 0 < lo i) ∧ (∀ i, lo i < hi i) ∧
      pi univ (fun i => Icc (lo i) (hi i)) ⊆ p.actions '' closedBall a0 r := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm : ∀ i, 0 < p.m i := hp.2.2
  set lo := p.actions (fun j => a0 j - r) with hlo
  set hi := p.actions (fun j => a0 j + r) with hhi
  have hlo2 : ∀ i, lo i ^ 2 = p.m i ^ 2 * p.kappa * (a0 i - r) := fun i =>
    p12c_actions_sq p hp _ i (by linarith [hpos i])
  have hhi2 : ∀ i, hi i ^ 2 = p.m i ^ 2 * p.kappa * (a0 i + r) := fun i =>
    p12c_actions_sq p hp _ i (by linarith [hpos i])
  have hlo0 : ∀ i, 0 < lo i := by
    intro i
    refine lt_of_le_of_ne (p12c_actions_nonneg p hp _ i) fun h => ?_
    have := hlo2 i
    rw [← h] at this
    have := hm i
    have := hpos i
    nlinarith [mul_pos (mul_pos (sq_pos_of_pos (hm i)) hk) (sub_pos.2 (hpos i))]
  refine ⟨lo, hi, hlo0, fun i => ?_, fun I hI => ?_⟩
  · refine lt_of_pow_lt_pow_left₀ 2 (p12c_actions_nonneg p hp _ i) ?_
    rw [hlo2, hhi2]
    have := mul_pos (sq_pos_of_pos (hm i)) hk
    nlinarith
  · have hIpos : ∀ i, 0 < I i := fun i => (hlo0 i).trans_le (hI i (mem_univ i)).1
    refine ⟨p.axes I, ?_, p11cB_actions_axes p hp hIpos⟩
    rw [mem_closedBall, dist_pi_le_iff hr.le]
    intro i
    rw [Real.dist_eq, abs_le]
    have hc := mul_pos (sq_pos_of_pos (hm i)) hk
    have h1 : lo i ^ 2 ≤ I i ^ 2 := pow_le_pow_left₀ (hlo0 i).le (hI i (mem_univ i)).1 2
    have h2 : I i ^ 2 ≤ hi i ^ 2 :=
      pow_le_pow_left₀ (hIpos i).le (hI i (mem_univ i)).2 2
    rw [hlo2] at h1
    rw [hhi2] at h2
    have hax : p.axes I i = I i ^ 2 / (p.m i ^ 2 * p.kappa) := rfl
    rw [hax, div_sub' hc.ne', le_div_iff₀ hc, div_le_iff₀ hc, sub_le_iff_le_add]
    constructor <;> nlinarith

end KAM.Planetary

end
