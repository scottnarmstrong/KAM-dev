/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Cauchy
public import KAM.Wave.Analytic.Flow.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Picard iterates for holomorphic vector fields

Blueprint-W `bpW:w1:flow`, steps `stepW:w1:flowlip` and `stepW:w1:picard` (package W1-ANALYTIC).
This is source-faithful infrastructure used by several nodes; the dependency graph is still being
built.

`KAM.Wave.FlowHyp X V U M δ` records the hypotheses of the blueprint lemma (`V` open, `X`
holomorphic on `V` with `‖X‖ ≤ M`, `U` open with margin `B(w, 2δ) ⊆ V` for `w ∈ U`, `0 < M < δ`).
`KAM.Wave.picard X w k t` are the Picard iterates `φ₀ = w`, `φ_{k+1}(t) = w + ∫₀ᵗ X (φ_k σ) dσ`. For
`w ∈ U` and `t ∈ [-1, 1]` they stay in `B(w, δ)` (`KAM.Wave.norm_picard_sub_le`), are continuous in
`t`, and `‖φ_{k+1} - φ_k‖ ≤ M L^k |t|^{k+1} / (k+1)!` with `L = M / δ`
(`KAM.Wave.norm_picard_succ_sub_le`).
-/

@[expose] public section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The hypotheses of blueprint `bpW:w1:flow`. -/
structure FlowHyp (X : F → F) (V U : Set F) (M δ : ℝ) : Prop where
  isOpen_V : IsOpen V
  isOpen_U : IsOpen U
  holo : DifferentiableOn ℂ X V
  bound : ∀ z ∈ V, ‖X z‖ ≤ M
  margin : ∀ w ∈ U, ball w (2 * δ) ⊆ V
  M_pos : 0 < M
  M_lt : M < δ

/-- The Picard iterates `φ₀ = w`, `φ_{k+1}(t) = w + ∫₀ᵗ X (φ_k σ) dσ`. -/
def picard (X : F → F) (w : F) : ℕ → ℝ → F
  | 0 => fun _ => w
  | k + 1 => fun t => w + ∫ σ in (0 : ℝ)..t, X (picard X w k σ)

@[simp] theorem picard_zero (X : F → F) (w : F) (t : ℝ) : picard X w 0 t = w := rfl

theorem picard_succ (X : F → F) (w : F) (k : ℕ) (t : ℝ) :
    picard X w (k + 1) t = w + ∫ σ in (0 : ℝ)..t, X (picard X w k σ) := rfl

namespace FlowHyp

variable {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

theorem delta_pos : 0 < δ := h.M_pos.trans h.M_lt

theorem ball_subset {w : F} (hw : w ∈ U) {z : F} (hz : z ∈ ball w δ) : ball z δ ⊆ V := fun y hy => by
  apply h.margin w hw
  rw [mem_ball, dist_eq_norm] at hy hz ⊢
  have := norm_add_le (y - z) (z - w)
  simp only [sub_add_sub_cancel] at this
  linarith

theorem lipschitz {w : F} (hw : w ∈ U) :
    ∀ x ∈ ball w δ, ∀ y ∈ ball w δ, ‖X x - X y‖ ≤ M / δ * ‖x - y‖ :=
  lipschitz_of_margin h.delta_pos h.M_pos.le h.isOpen_V h.holo h.bound (convex_ball w δ)
    fun _ hz => h.ball_subset hw hz

theorem fderiv_le {w : F} (hw : w ∈ U) {z : F} (hz : z ∈ ball w δ) : ‖fderiv ℂ X z‖ ≤ M / δ :=
  norm_fderiv_le_div_of_ball_subset h.delta_pos h.M_pos.le h.holo h.bound (h.ball_subset hw hz)

theorem mem_V {w : F} (hw : w ∈ U) {z : F} (hz : z ∈ ball w δ) : z ∈ V :=
  h.ball_subset hw hz (mem_ball_self h.delta_pos)

theorem continuousOn_X : ContinuousOn X V := h.holo.continuousOn

end FlowHyp

end KAM.Wave
