/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Planetary.PG.Setting
public import KAM.Planetary.PGAssembly.ExtensionTube
public import KAM.Planetary.PGAssembly.Extension

/-!
# P Part 5: complex Lipschitz bounds and the complex fast frequency map
(`bpP:p5:lip-complex`, `bpP:p5:bilip`)

`lip_complex`: a bounded holomorphic map on `actionNbhd X (2ρ)` is Lipschitz on `actionNbhd X ρ`
(Cauchy estimate on closed polydiscs for close pairs, the sup bound for far pairs).
`complexFast`, `bilip`: the complex fast frequency map `∂H̃₀` of the extension is bi-Lipschitz on
`actionNbhd (closure V) ρ` with `‖∂²H̃₀‖` bounded on `actionNbhd (closure V) (2ρ)`
(steps `bl-real`, `bl-comp`: injectivity and invertible derivative at real points from the frozen
inverse; a compactness contradiction with the local linearisation).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BL.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

/-- Cauchy estimate: a holomorphic map bounded by `A` on a closed polydisc of radius `r` about `w`
has derivative of norm at most `A / r` at `w`. -/
theorem norm_fderiv_le_of_closedBall {N m : ℕ} {U : Set (Fin N → ℂ)} {f : (Fin N → ℂ) → Fin m → ℂ}
    {w : Fin N → ℂ} {r A : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f U)
    (hball : closedBall w r ⊆ U) (hb : ∀ z ∈ closedBall w r, ‖f z‖ ≤ A) :
    ‖fderiv ℂ f w‖ ≤ A / r := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb w (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hA hr.le) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R : ℝ := r / ‖v‖ with hR
  have hRpos : 0 < R := div_pos hr hvpos
  set g : ℂ → Fin m → ℂ := fun t => f (w + t • v) with hg
  have hmaps : ∀ t : ℂ, ‖t‖ ≤ R → w + t • v ∈ closedBall w r := by
    intro t ht
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right ht hvpos.le
      _ = r := by rw [hR]; field_simp
  have hgd : DifferentiableOn ℂ g (closedBall 0 R) := by
    refine hf.comp ?_ (fun t ht => hball (hmaps t (by simpa using ht)))
    exact ((differentiable_const w).add (differentiable_id.smul_const v)).differentiableOn
  have hdc : DiffContOnCl ℂ g (ball 0 R) := by
    refine ⟨hgd.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball 0 hRpos.ne']
    exact hgd.continuousOn
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc
    (C := A) (fun t ht => hb _ (hmaps t (by rw [mem_sphere_zero_iff_norm] at ht; exact ht.le)))
  have hfd : DifferentiableAt ℂ f w := (hf.differentiableAt (by
    exact mem_of_superset (closedBall_mem_nhds w hr) hball))
  have hderiv : deriv g 0 = fderiv ℂ f w v := by
    have h1 : HasDerivAt (fun t : ℂ => w + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add w
    have h2 : HasFDerivAt f (fderiv ℂ f w) (w + (0:ℂ) • v) := by
      simpa using hfd.hasFDerivAt
    exact (h2.comp_hasDerivAt (0:ℂ) h1).deriv
  rw [hderiv] at hCauchy
  calc ‖fderiv ℂ f w v‖ ≤ A / R := hCauchy
    _ = A / r * ‖v‖ := by rw [hR]; field_simp

theorem lip_complex {m N : ℕ} (hN : 0 < N) {X : Set (Fin N → ℝ)} {rho A : ℝ}
    (hrho : 0 < rho) {f : (Fin N → ℂ) → Fin m → ℂ}
    (hf : DifferentiableOn ℂ f (KAM.actionNbhd X (2*rho)))
    (hb : ∀ z ∈ KAM.actionNbhd X (2*rho), ‖f z‖ ≤ A) :
    ∀ z ∈ KAM.actionNbhd X rho, ∀ z' ∈ KAM.actionNbhd X rho,
      ‖f z-f z'‖ ≤ (2*N*A/rho)*‖z-z'‖ := by
  intro z hz z' hz'
  have hzU : z ∈ KAM.actionNbhd X (2*rho) := by
    obtain ⟨J, hJ, hzJ⟩ := hz
    exact ⟨J, hJ, by linarith⟩
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb z hzU)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hcoef : 2 * A / rho ≤ 2 * N * A / rho := by
    apply div_le_div_of_nonneg_right _ hrho.le
    nlinarith
  have hmono : ∀ {e : Fin N → ℂ}, e ∈ KAM.actionNbhd X rho → ∀ {w : Fin N → ℂ},
      ‖w - e‖ < rho / 2 → closedBall w (rho / 2) ⊆ KAM.actionNbhd X (2*rho) := by
    intro e he w hwe u hu
    obtain ⟨J, hJ, heJ⟩ := he
    refine ⟨J, hJ, ?_⟩
    have heJ' : ‖e - KAM.realInclusion N J‖ < rho := heJ
    rw [mem_closedBall_iff_norm] at hu
    calc ‖u - KAM.realInclusion N J‖ = ‖(u - w) + (w - e) + (e - KAM.realInclusion N J)‖ := by
          congr 1; abel
      _ ≤ ‖u - w‖ + ‖w - e‖ + ‖e - KAM.realInclusion N J‖ := norm_add₃_le
      _ < 2 * rho := by linarith
  by_cases hclose : ‖z - z'‖ < rho
  · -- close pair: Cauchy on the segment, mean value inequality
    have hseg : ∀ w ∈ segment ℝ z z', DifferentiableAt ℂ f w ∧ ‖fderiv ℂ f w‖ ≤ 2 * A / rho := by
      intro w hw
      have hsum := dist_add_dist_of_mem_segment hw
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hsum
      have hsub : closedBall w (rho / 2) ⊆ KAM.actionNbhd X (2*rho) := by
        by_cases hwz : ‖z - w‖ ≤ ‖w - z'‖
        · exact hmono hz (by rw [norm_sub_rev]; linarith)
        · exact hmono hz' (by linarith)
      refine ⟨hf.differentiableAt (mem_of_superset (closedBall_mem_nhds w (by positivity)) hsub),
        ?_⟩
      have := norm_fderiv_le_of_closedBall (by positivity : 0 < rho / 2) hf hsub
        (fun u hu => hb u (hsub hu))
      calc ‖fderiv ℂ f w‖ ≤ A / (rho / 2) := this
        _ = 2 * A / rho := by field_simp
    have key := (convex_segment z z').norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => (hseg w hw).1) (fun w hw => (hseg w hw).2) (left_mem_segment ℝ z z')
      (right_mem_segment ℝ z z')
    rw [norm_sub_rev, norm_sub_rev z z']
    exact key.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  · -- far pair: the sup bound
    replace hclose := not_lt.1 hclose
    have hz'U : z' ∈ KAM.actionNbhd X (2*rho) := by
      obtain ⟨J, hJ, hzJ⟩ := hz'
      exact ⟨J, hJ, by linarith⟩
    calc ‖f z - f z'‖ ≤ ‖f z‖ + ‖f z'‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith [hb z hzU, hb z' hz'U]
      _ = (2 * A / rho) * rho := by field_simp
      _ ≤ (2 * A / rho) * ‖z - z'‖ := mul_le_mul_of_nonneg_left hclose (by positivity)
      _ ≤ (2 * N * A / rho) * ‖z - z'‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

end KAM.Planetary

end
