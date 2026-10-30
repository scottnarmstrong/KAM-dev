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

Blueprint-W `bpW:w1:flow`, steps `stepW:w1:flowlip` and `stepW:w1:wavePicard` (package W1-ANALYTIC).
This is source-faithful infrastructure used by several nodes; the dependency graph is still being
built.

`KAM.Wave.FlowHyp X V U M δ` records the hypotheses of the blueprint lemma (`V` open, `X`
holomorphic on `V` with `‖X‖ ≤ M`, `U` open with margin `B(w, 2δ) ⊆ V` for `w ∈ U`, `0 < M < δ`).
`KAM.Wave.wavePicard X w k t` are the Picard iterates `φ₀ = w`,
`φ_{k+1}(t) = w + ∫₀ᵗ X (φ_k σ) dσ`. For
`w ∈ U` and `t ∈ [-1, 1]` they stay in `B(w, δ)` (`KAM.Wave.norm_picard_sub_le`), are continuous in
`t`, and `‖φ_{k+1} - φ_k‖ ≤ M L^k |t|^{k+1} / (k+1)!` with `L = M / δ`
(`KAM.Wave.norm_picard_succ_sub_le`).
-/

@[expose] public noncomputable section

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
def wavePicard (X : F → F) (w : F) : ℕ → ℝ → F
  | 0 => fun _ => w
  | k + 1 => fun t => w + ∫ σ in (0 : ℝ)..t, X (wavePicard X w k σ)

@[simp] theorem wavePicard_zero (X : F → F) (w : F) (t : ℝ) : wavePicard X w 0 t = w := rfl

theorem wavePicard_succ (X : F → F) (w : F) (k : ℕ) (t : ℝ) :
    wavePicard X w (k + 1) t = w + ∫ σ in (0 : ℝ)..t, X (wavePicard X w k σ) := rfl

namespace FlowHyp

variable {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

theorem delta_pos : 0 < δ := h.M_pos.trans h.M_lt

theorem ball_subset_V {w : F} (hw : w ∈ U) {z : F} (hz : z ∈ ball w δ) :
    ball z δ ⊆ V := fun y hy => by
  apply h.margin w hw
  rw [mem_ball, dist_eq_norm] at hy hz ⊢
  have := norm_add_le (y - z) (z - w)
  simp only [sub_add_sub_cancel] at this
  linarith

theorem lipschitzOn_ball {w : F} (hw : w ∈ U) :
    ∀ x ∈ ball w δ, ∀ y ∈ ball w δ, ‖X x - X y‖ ≤ M / δ * ‖x - y‖ :=
  lipschitz_of_margin h.delta_pos h.M_pos.le h.isOpen_V h.holo h.bound (convex_ball w δ)
    fun _ hz => h.ball_subset_V hw hz

theorem norm_fderiv_le_ball {w : F} (hw : w ∈ U) {z : F} (hz : z ∈ ball w δ) :
    ‖fderiv ℂ X z‖ ≤ M / δ :=
  norm_fderiv_le_div_of_ball_subset h.delta_pos h.M_pos.le h.holo h.bound (h.ball_subset_V hw hz)

theorem mem_V_of_ball {w : F} (hw : w ∈ U) {z : F} (hz : z ∈ ball w δ) : z ∈ V :=
  h.ball_subset_V hw hz (mem_ball_self h.delta_pos)

theorem continuousOn_X : ContinuousOn X V := h.holo.continuousOn

end FlowHyp


section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuousOn_wavePrimitive {g : ℝ → E}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    ContinuousOn (fun t => ∫ σ in (0 : ℝ)..t, g σ) (Icc (-1) 1) := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := 0)
    (hg.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1) |>.mono_set
      (by rw [hu]))
    (by rw [hu]; exact ⟨by norm_num, by norm_num⟩)
  rwa [hu] at this

theorem uIoc_subset_Icc {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : Ι 0 t ⊆ Icc (-1) 1 :=
  (uIoc_subset_uIcc).trans (uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht)

theorem uIcc_subset_Icc' {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : uIcc 0 t ⊆ Icc (-1) 1 :=
  uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht

end Helpers

section Iterates

variable {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

/-- The iterates stay within distance `M |t|` of `w`, and are continuous in `t`. -/
theorem norm_picard_sub_le {w : F} (hw : w ∈ U) : ∀ k : ℕ,
    (∀ t ∈ Icc (-1 : ℝ) 1, ‖wavePicard X w k t - w‖ ≤ M * |t|) ∧
      ContinuousOn (wavePicard X w k) (Icc (-1) 1)
  | 0 => ⟨fun t _ => by simpa using mul_nonneg h.M_pos.le (abs_nonneg t), continuousOn_const⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := norm_picard_sub_le hw k
    have hmem : ∀ t ∈ Icc (-1 : ℝ) 1, wavePicard X w k t ∈ ball w δ := fun t ht => by
      rw [mem_ball_iff_norm]
      refine lt_of_le_of_lt (h1 t ht) ?_
      have : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
      nlinarith [h.M_lt, h.M_pos]
    have hg : ContinuousOn (fun σ => X (wavePicard X w k σ)) (Icc (-1) 1) :=
      h.continuousOn_X.comp h2 fun t ht => h.mem_V_of_ball hw (hmem t ht)
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [wavePicard_succ, add_sub_cancel_left]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M)
        (f := fun σ => X (wavePicard X w k σ)) fun σ hσ => h.bound _ (h.mem_V_of_ball hw (hmem σ
          (uIoc_subset_Icc ht hσ)))
      simpa [mul_comm] using this
    · exact continuousOn_const.add (continuousOn_wavePrimitive hg)

theorem picard_mem_ball {w : F} (hw : w ∈ U) (k : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    wavePicard X w k t ∈ ball w δ := by
  rw [mem_ball_iff_norm]
  refine lt_of_le_of_lt ((norm_picard_sub_le h hw k).1 t ht) ?_
  have : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  nlinarith [h.M_lt, h.M_pos]

theorem continuousOn_X_picard {w : F} (hw : w ∈ U) (k : ℕ) :
    ContinuousOn (fun σ => X (wavePicard X w k σ)) (Icc (-1) 1) :=
  h.continuousOn_X.comp (norm_picard_sub_le h hw k).2 fun _ ht =>
    h.mem_V_of_ball hw (picard_mem_ball h hw k ht)

/-- Successive differences of the Picard iterates (blueprint `stepW:w1:wavePicard`). -/
theorem norm_picard_succ_sub_le {w : F} (hw : w ∈ U) : ∀ k : ℕ, ∀ t ∈ Icc (-1 : ℝ) 1,
    ‖wavePicard X w (k + 1) t - wavePicard X w k t‖ ≤
      M * (M / δ) ^ k * |t| ^ (k + 1) / ((k + 1).factorial : ℝ)
  | 0, t, ht => by
    have := norm_integral_le_pow (f := fun σ => X (wavePicard X w 0 σ)) (c := M) (m := 0) (t := t)
      (fun σ hσ => by simpa using h.bound _ (h.mem_V_of_ball hw (picard_mem_ball h hw 0
        (uIoc_subset_Icc ht hσ))))
    rw [wavePicard_succ, wavePicard_zero, add_sub_cancel_left]
    simpa using this
  | k + 1, t, ht => by
    have hint : ∀ j, IntervalIntegrable (fun σ => X (wavePicard X w j σ)) volume 0 t := fun j =>
      ((continuousOn_X_picard h hw j).mono (uIcc_subset_Icc' ht)).intervalIntegrable
    have hdiff : wavePicard X w (k + 2) t - wavePicard X w (k + 1) t =
        ∫ σ in (0 : ℝ)..t, (X (wavePicard X w (k + 1) σ) - X (wavePicard X w k σ)) := by
      rw [wavePicard_succ X w (k + 1), wavePicard_succ X w k, add_sub_add_left_eq_sub,
        intervalIntegral.integral_sub (hint (k + 1)) (hint k)]
    rw [hdiff]
    have hfac : ((k + 2).factorial : ℝ) = (k + 2) * (k + 1).factorial := by
      rw [Nat.factorial_succ (k + 1)]; push_cast; ring
    have hfpos : (0 : ℝ) < (k + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have := norm_integral_le_pow
      (f := fun σ => X (wavePicard X w (k + 1) σ) - X (wavePicard X w k σ))
      (c := M * (M / δ) ^ (k + 1) / ((k + 1).factorial : ℝ)) (m := k + 1) (t := t)
      (fun σ hσ => by
        have hσ' := uIoc_subset_Icc ht hσ
        have h1 := h.lipschitzOn_ball hw _ (picard_mem_ball h hw (k + 1) hσ') _
          (picard_mem_ball h hw k hσ')
        have h2 := norm_picard_succ_sub_le hw k σ hσ'
        refine h1.trans ?_
        calc M / δ * ‖wavePicard X w (k + 1) σ - wavePicard X w k σ‖
            ≤ M / δ * (M * (M / δ) ^ k * |σ| ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 (div_nonneg h.M_pos.le h.delta_pos.le)
          _ = M * (M / δ) ^ (k + 1) / ((k + 1).factorial : ℝ) * |σ| ^ (k + 1) := by ring)
    refine this.trans_eq ?_
    rw [show k + 1 + 1 = k + 2 by rfl, hfac]
    push_cast
    field_simp
    ring

end Iterates

end KAM.Wave
