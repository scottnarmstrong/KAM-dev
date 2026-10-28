/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Planetary.PGAssembly.ComplexLocal
public import KAM.Planetary.PGAssembly.RealSlice

/-!
# P Part 5: compact real complexification (`bpP:p5:ext-loc`, helper)

`compact_real_complexification`: a function real-analytic near a compact `X ⊆ ℝᴺ` is the real
restriction of a function holomorphic and bounded on a complex tube `actionNbhd X ρ`.

Proof: `local_real_complexification` at each point of `X`, a finite subcover by half-radius real
balls, a uniform radius (the least half-radius), and gluing: two local complexifications agree on
the (convex, hence connected) overlap of their complex balls by `real_slice_identity`, because the
overlap contains a real point (the componentwise real part of any overlap point).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CG.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

/-- Two local complexifications of the same real function agree on the overlap of their balls. -/
theorem local_complexifications_agree {N : ℕ} {f : (Fin N → ℝ) → ℝ} {x y : Fin N → ℝ}
    {rx ry : ℝ} {Fx Fy : (Fin N → ℂ) → ℂ}
    (hFx : DifferentiableOn ℂ Fx (ball (KAM.realInclusion N x) rx))
    (hFy : DifferentiableOn ℂ Fy (ball (KAM.realInclusion N y) ry))
    (hx : ∀ z ∈ ball x rx, Fx (KAM.realInclusion N z) = (f z : ℂ))
    (hy : ∀ z ∈ ball y ry, Fy (KAM.realInclusion N z) = (f z : ℂ)) :
    EqOn Fx Fy (ball (KAM.realInclusion N x) rx ∩ ball (KAM.realInclusion N y) ry) := by
  have hU : IsOpen (ball (KAM.realInclusion N x) rx ∩ ball (KAM.realInclusion N y) ry) :=
    isOpen_ball.inter isOpen_ball
  have hUc : IsPreconnected (ball (KAM.realInclusion N x) rx ∩ ball (KAM.realInclusion N y) ry) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  by_cases hne : (ball (KAM.realInclusion N x) rx ∩ ball (KAM.realInclusion N y) ry).Nonempty
  · obtain ⟨w, hwx, hwy⟩ := hne
    refine real_slice_identity hU hUc (hFx.mono inter_subset_left) (hFy.mono inter_subset_right)
      (V := ball x rx ∩ ball y ry) (isOpen_ball.inter isOpen_ball)
      ⟨KAM.realPartCLM N w, ?_, ?_⟩ ?_ ?_
    · rw [mem_ball_iff_norm] at hwx ⊢
      have := KAM.norm_realPartCLM_le (w - KAM.realInclusion N x)
      rw [map_sub, KAM.realPartCLM_realInclusion] at this
      exact this.trans_lt hwx
    · rw [mem_ball_iff_norm] at hwy ⊢
      have := KAM.norm_realPartCLM_le (w - KAM.realInclusion N y)
      rw [map_sub, KAM.realPartCLM_realInclusion] at this
      exact this.trans_lt hwy
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨realInclusion_mem_ball_iff.2 hz.1, realInclusion_mem_ball_iff.2 hz.2⟩
    · intro z hz
      rw [hx z hz.1, hy z hz.2]
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact eqOn_empty _ _

/-- A positive lower bound for finitely many positive radii. -/
theorem exists_pos_le_finset {α : Type*} [DecidableEq α] (ρ : α → ℝ) (t : Finset α)
    (h : ∀ x ∈ t, 0 < ρ x) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ t, r ≤ ρ i / 2 := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨r, hr, hs⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    have ha0 := h a (Finset.mem_insert_self a s)
    refine ⟨min r (ρ a / 2), lt_min hr (half_pos ha0), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs i hi)

/-- Explicit classical input for ext-loc, including the uniform bound. -/
theorem compact_real_complexification {N : ℕ} {X : Set (Fin N → ℝ)}
    (hX : IsCompact X) {f : (Fin N → ℝ) → ℝ} (hf : AnalyticOnNhd ℝ f X) :
    ∃ (rho M : ℝ) (F : (Fin N → ℂ) → ℂ), 0 < rho ∧ 0 < M ∧
      DifferentiableOn ℂ F (KAM.actionNbhd X rho) ∧
      (∀ x : Fin N → ℝ, KAM.realInclusion N x ∈ KAM.actionNbhd X rho →
        F (KAM.realInclusion N x) = (f x:ℂ)) ∧
      (∀ z ∈ KAM.actionNbhd X rho, ‖F z‖ ≤ M) := by
  classical
  have loc : ∀ x : Fin N → ℝ, ∃ (ρ M : ℝ) (F : (Fin N → ℂ) → ℂ), x ∈ X →
      (0 < ρ ∧ 0 < M ∧ DifferentiableOn ℂ F (ball (KAM.realInclusion N x) ρ) ∧
      (∀ y ∈ ball x ρ, F (KAM.realInclusion N y) = (f y : ℂ)) ∧
      (∀ z ∈ ball (KAM.realInclusion N x) ρ, ‖F z‖ ≤ M)) := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨ρ, M, F, h⟩ := local_real_complexification (hf x hx)
      exact ⟨ρ, M, F, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hx⟩
  choose ρ M F h using loc
  obtain ⟨t, htX, hcov⟩ := hX.elim_nhds_subcover (fun x => ball x (ρ x / 2))
    fun x hx => ball_mem_nhds _ (half_pos (h x hx).1)
  obtain ⟨r, hr0, hr⟩ := exists_pos_le_finset ρ t fun x hx => (h x (htX x hx)).1
  -- the tube lies in the union of the complex balls
  have hcover : ∀ z ∈ KAM.actionNbhd X r, ∃ i ∈ t, z ∈ ball (KAM.realInclusion N i) (ρ i) := by
    rintro z ⟨J, hJ, hzJ⟩
    have hJc := mem_iUnion₂.1 (hcov hJ)
    obtain ⟨i, hit, hJi⟩ := hJc
    refine ⟨i, hit, ?_⟩
    rw [mem_ball_iff_norm]
    have h1 : ‖z - KAM.realInclusion N J‖ < r := hzJ
    have h2 : ‖KAM.realInclusion N J - KAM.realInclusion N i‖ < ρ i / 2 := by
      rw [← map_sub, KAM.norm_realInclusion]; exact mem_ball_iff_norm.1 hJi
    calc ‖z - KAM.realInclusion N i‖
        = ‖(z - KAM.realInclusion N J) + (KAM.realInclusion N J - KAM.realInclusion N i)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖z - KAM.realInclusion N J‖ + ‖KAM.realInclusion N J - KAM.realInclusion N i‖ :=
          norm_add_le _ _
      _ < r + ρ i / 2 := add_lt_add h1 h2
      _ ≤ ρ i := by linarith [hr i hit]
  -- glued function
  let idx : (Fin N → ℂ) → (Fin N → ℝ) := fun z =>
    if hz : ∃ i ∈ t, z ∈ ball (KAM.realInclusion N i) (ρ i) then hz.choose else 0
  let G : (Fin N → ℂ) → ℂ := fun z => F (idx z) z
  have hG : ∀ i ∈ t, ∀ w ∈ ball (KAM.realInclusion N i) (ρ i), G w = F i w := by
    intro i hit w hw
    have hex : ∃ j ∈ t, w ∈ ball (KAM.realInclusion N j) (ρ j) := ⟨i, hit, hw⟩
    have hspec := hex.choose_spec
    have hidx : idx w = hex.choose := by simp only [idx, hex, dite_true]
    show F (idx w) w = F i w
    rw [hidx]
    have hj := htX _ hspec.1
    exact local_complexifications_agree (f := f) (h _ hj).2.2.1 (h i (htX i hit)).2.2.1
      (h _ hj).2.2.2.1 (h i (htX i hit)).2.2.2.1 ⟨hspec.2, hw⟩
  refine ⟨r, 1 + ∑ i ∈ t, M i, G, hr0, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ ∑ i ∈ t, M i := Finset.sum_nonneg fun i hi => (h i (htX i hi)).2.1.le
    linarith
  · intro z hz
    obtain ⟨i, hit, hzi⟩ := hcover z hz
    have hdiff : DifferentiableOn ℂ G (ball (KAM.realInclusion N i) (ρ i)) :=
      (h i (htX i hit)).2.2.1.congr fun w hw => hG i hit w hw
    exact (hdiff.differentiableAt (isOpen_ball.mem_nhds hzi)).differentiableWithinAt
  · intro x hx
    obtain ⟨i, hit, hxi⟩ := hcover _ hx
    rw [hG i hit _ hxi]
    exact (h i (htX i hit)).2.2.2.1 x (realInclusion_mem_ball_iff.1 hxi)
  · intro z hz
    obtain ⟨i, hit, hzi⟩ := hcover z hz
    rw [hG i hit _ hzi]
    have hle := (h i (htX i hit)).2.2.2.2 z hzi
    have : M i ≤ ∑ j ∈ t, M j :=
      Finset.single_le_sum (f := M) (fun j hj => (h j (htX j hj)).2.1.le) hit
    linarith

end KAM.Planetary

end
