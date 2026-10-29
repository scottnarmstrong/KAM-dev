/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Strip.AnalyticTaylor

/-!
# Holomorphic extension of the secular rotation (P11A-P2, `stepP:p11:hc-rot`)

A real analytic family of matrices `R` on a real ball extends entrywise to a holomorphic family
`ρ` on a complex max-norm ball (`p11_complexification`); the polynomial identity `RᵀR = 1`
persists to the complex ball (`p11_real_slice_identity`), so `ρ` takes values in `O(n, ℂ)`
(`p11_rotation_complex`). The constants `B_ρ`, `B'_ρ` are compactness bounds on a smaller closed
ball (`p11_rotation_bounds`).
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Rotation

variable {n : ℕ}

/-- `hc-rot`: complexification of an analytic rotation family with complex orthogonality. -/
theorem p11_rotation_complex {x0 : P11Vec n} {t1 : ℝ} (ht1 : 0 < t1)
    {R : P11Vec n → Matrix (Fin n) (Fin n) ℝ}
    (hR : ∀ i j, AnalyticOnNhd ℝ (fun x => R x i j) (Metric.ball x0 t1))
    (hO : ∀ x ∈ Metric.ball x0 t1, (R x).transpose * R x = 1) :
    ∃ t2 : ℝ, 0 < t2 ∧ t2 ≤ t1 ∧ ∃ ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ,
      (∀ i j, DifferentiableOn ℂ (fun z => ρ z i j) (Metric.ball (KAM.realInclusion n x0) t2)) ∧
      DifferentiableOn ℂ ρ (Metric.ball (KAM.realInclusion n x0) t2) ∧
      (∀ y, ‖y - x0‖ < t2 → ρ (KAM.realInclusion n y) = (R y).map (fun r : ℝ => (r : ℂ))) ∧
      ∀ z ∈ Metric.ball (KAM.realInclusion n x0) t2, (ρ z).transpose * ρ z = 1 := by
  have hent : ∀ ij : Fin n × Fin n, ∃ r : ℝ, 0 < r ∧ ∃ F : P11CVec n → P11CVec 1,
      DifferentiableOn ℂ F (Metric.ball (KAM.realInclusion n x0) r) ∧
      ∀ y, ‖y - x0‖ < r →
        F (KAM.realInclusion n y) = KAM.realInclusion 1 (fun _ => R y ij.1 ij.2) := by
    intro ij
    refine p11_complexification (f := fun y : P11Vec n => fun _ : Fin 1 => R y ij.1 ij.2)
      (x := x0) ?_
    refine analyticAt_pi_iff.2 fun _ => ?_
    exact hR ij.1 ij.2 x0 (Metric.mem_ball_self ht1)
  choose r hr F hF hFeq using hent
  have hsmall : ∃ t2 : ℝ, 0 < t2 ∧ t2 ≤ t1 ∧ ∀ ij, t2 ≤ r ij := by
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ t1 ∧ ∀ ij, t ≤ r ij := by
      have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), t ≤ t1 := Iic_mem_nhds ht1
      refine (h1.filter_mono nhdsWithin_le_nhds).and ?_
      refine eventually_all.2 fun ij => ?_
      have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t ≤ r ij := Iic_mem_nhds (hr ij)
      exact h2.filter_mono nhdsWithin_le_nhds
    obtain ⟨t, ht, htpos⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨t, htpos, ht.1, ht.2⟩
  obtain ⟨t2, ht2, ht21, ht2r⟩ := hsmall
  have hmono : ∀ ij, Metric.ball (KAM.realInclusion n x0) t2 ⊆
      Metric.ball (KAM.realInclusion n x0) (r ij) := fun ij => Metric.ball_subset_ball (ht2r ij)
  let ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ := fun z i j => F (i, j) z 0
  have hreal : ∀ y, ‖y - x0‖ < t2 → ρ (KAM.realInclusion n y) =
      (R y).map (fun r : ℝ => (r : ℂ)) := by
    intro y hy
    ext i j
    simp only [ρ, hFeq (i, j) y (lt_of_lt_of_le hy (ht2r _)), Matrix.map_apply,
      KAM.realInclusion_apply]
  have hdiff : ∀ i j, DifferentiableOn ℂ (fun z => ρ z i j)
      (Metric.ball (KAM.realInclusion n x0) t2) := fun i j =>
    (differentiableOn_pi.1 ((hF (i, j)).mono (hmono (i, j)))) 0
  refine ⟨t2, ht2, ht21, ρ, hdiff, ?_, hreal, ?_⟩
  · exact differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hdiff i j
  · intro z hz
    ext i j
    have hG : ∀ z ∈ Metric.ball (KAM.realInclusion n x0) t2,
        ∑ k, ρ z k i * ρ z k j - (if i = j then 1 else 0) = 0 := by
      refine p11_real_slice_identity ht2 (F := fun z => ∑ k, ρ z k i * ρ z k j -
        (if i = j then 1 else 0)) ?_ ?_
      · exact (DifferentiableOn.fun_sum fun k _ => (hdiff k i).mul (hdiff k j)).sub
          (differentiableOn_const _)
      · intro y hy
        have hyb : y ∈ Metric.ball x0 t1 := by
          rw [mem_ball_iff_norm]; exact lt_of_lt_of_le hy ht21
        have h1 := congrFun (congrFun (hO y hyb) i) j
        have h1' : ∑ k, R y k i * R y k j = if i = j then 1 else 0 := by
          simpa [Matrix.mul_apply, Matrix.one_apply] using h1
        have hc : ∑ k, ((R y k i : ℝ) : ℂ) * (R y k j : ℂ) =
            ((∑ k, R y k i * R y k j : ℝ) : ℂ) := by push_cast; rfl
        simp only [hreal y hy, Matrix.map_apply]
        rw [hc, h1']
        split_ifs <;> simp
    have := hG z hz
    simpa [Matrix.mul_apply, Matrix.one_apply, sub_eq_zero] using this

open scoped Matrix.Norms.Elementwise in
/-- `hc-rot`: the constants `B_ρ`, `B'_ρ` are compactness bounds on a smaller closed ball. -/
theorem p11_rotation_bounds {x0 : P11Vec n} {t2 r : ℝ} (hrt : r < t2)
    {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ}
    (hρ : ∀ i j, DifferentiableOn ℂ (fun z => ρ z i j)
      (Metric.ball (KAM.realInclusion n x0) t2)) :
    ∃ B B' : ℝ, 1 ≤ B ∧ 1 ≤ B' ∧ ∀ J ∈ Metric.ball (KAM.realInclusion n x0) r,
      (∀ i, ∑ j, ‖ρ J i j‖ ≤ B) ∧
      ∀ l i, ∑ j, ‖((ρ J).transpose * fderiv ℂ ρ J (Pi.single l 1)) i j‖ ≤ B' := by
  set c := KAM.realInclusion n x0 with hc
  have hK : IsCompact (Metric.closedBall c r) := isCompact_closedBall _ _
  have hsub : Metric.closedBall c r ⊆ Metric.ball c t2 := Metric.closedBall_subset_ball hrt
  have hopen : IsOpen (Metric.ball c t2) := Metric.isOpen_ball
  have hCD : ContDiffOn ℂ 1 ρ (Metric.ball c t2) :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j =>
      (analyticOnNhd_of_differentiableOn hopen (hρ i j)).contDiffOn_of_completeSpace
  have hcont : ContinuousOn ρ (Metric.ball c t2) := hCD.continuousOn
  have hfd : ContinuousOn (fun J => fderiv ℂ ρ J) (Metric.ball c t2) :=
    hCD.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hent : ∀ i j, ContinuousOn (fun J => ρ J i j) (Metric.ball c t2) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hcont)
  have hfent : ∀ l k j, ContinuousOn (fun J => fderiv ℂ ρ J (Pi.single l 1) k j)
      (Metric.ball c t2) := fun l k j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply k).comp_continuousOn
      (hfd.clm_apply continuousOn_const))
  have hΨ : ContinuousOn (fun J => ∑ i, ∑ j, ‖ρ J i j‖) (Metric.ball c t2) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => (hent i j).norm
  have hΦ : ContinuousOn (fun J => ∑ l, ∑ i, ∑ j,
      ‖∑ k, ρ J k i * fderiv ℂ ρ J (Pi.single l 1) k j‖) (Metric.ball c t2) :=
    continuousOn_finsetSum _ fun l _ => continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ => (continuousOn_finsetSum _ fun k _ =>
        (hent k i).mul (hfent l k j)).norm
  obtain ⟨b1, hb1⟩ := hK.exists_bound_of_continuousOn (hΨ.mono hsub)
  obtain ⟨b2, hb2⟩ := hK.exists_bound_of_continuousOn (hΦ.mono hsub)
  refine ⟨max 1 b1, max 1 b2, le_max_left _ _, le_max_left _ _, fun J hJ => ⟨fun i => ?_,
    fun l i => ?_⟩⟩
  · have hJ' : J ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hJ
    have h1 := hb1 J hJ'
    have hn1 : 0 ≤ ∑ i, ∑ j, ‖ρ J i j‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_of_nonneg hn1] at h1
    calc ∑ j, ‖ρ J i j‖ ≤ ∑ i', ∑ j, ‖ρ J i' j‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j, ‖ρ J i' j‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ max 1 b1 := h1.trans (le_max_right _ _)
  · have hJ' : J ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hJ
    have h2 := hb2 J hJ'
    have hn2 : 0 ≤ ∑ l, ∑ i, ∑ j, ‖∑ k, ρ J k i * fderiv ℂ ρ J (Pi.single l 1) k j‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_of_nonneg hn2] at h2
    have e : ∀ j, ((ρ J).transpose * fderiv ℂ ρ J (Pi.single l 1)) i j =
        ∑ k, ρ J k i * fderiv ℂ ρ J (Pi.single l 1) k j := fun j => by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [e]
    calc ∑ j, ‖∑ k, ρ J k i * fderiv ℂ ρ J (Pi.single l 1) k j‖
        ≤ ∑ i', ∑ j, ‖∑ k, ρ J k i' * fderiv ℂ ρ J (Pi.single l 1) k j‖ :=
          Finset.single_le_sum
            (f := fun i' => ∑ j, ‖∑ k, ρ J k i' * fderiv ℂ ρ J (Pi.single l 1) k j‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ l', ∑ i', ∑ j, ‖∑ k, ρ J k i' * fderiv ℂ ρ J (Pi.single l' 1) k j‖ :=
          Finset.single_le_sum
            (f := fun l' => ∑ i', ∑ j, ‖∑ k, ρ J k i' * fderiv ℂ ρ J (Pi.single l' 1) k j‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ l)
      _ ≤ max 1 b2 := h2.trans (le_max_right _ _)

end Rotation

end KAM.Planetary

end
