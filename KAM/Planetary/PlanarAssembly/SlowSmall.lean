/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff

/-!
# Planar assembly: smallness of the slow part of the Birkhoff map (Part 12)

Blueprint P, Part 12 (`stepP:p12:ch-tube`).  For the map `T = Φ_ρ⁻¹ ∘ Φ_χ` of the normal form
(`p11c_rotationLift p ∘ p11c_liftFlow chi.eval`), the slow part of `T w` depends only on the
action and slow part of `w`, and vanishes where the slow part of `w` does (the quartic Hamiltonian
field vanishes at the origin).  By uniform continuity on a compact action set, the slow part of
`T w` is uniformly small when that of `w` is small.  This is the forward-tube input
`Γ_i (T w) ≤ δ`.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

theorem p12c_flow_zero {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {I : Fin 2 → ℝ}
    (hI : I ∈ O) : p11c_flow chi.eval I 1 0 = 0 := by
  have hv0 : hamiltonianVectorField (chi.eval I) 0 = 0 := by
    have := p11cQ_field_smul chi hI (s := 2) two_ne_zero 0
    simp only [smul_zero] at this
    have h8 : (7 : ℝ) • hamiltonianVectorField (chi.eval I) 0 = 0 := by
      rw [show (7 : ℝ) = 2 ^ 3 - 1 by norm_num, sub_smul, ← this]; simp
    exact (smul_eq_zero.1 h8).resolve_left (by norm_num)
  have hsol : IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Icc (-1) 1)
      (fun _ : ℝ => (0 : Phase 2)) := fun t _ => by
    refine ⟨mem_univ _, ?_⟩
    show HasDerivAt (fun _ : ℝ => (0 : Phase 2)) (hamiltonianVectorField (chi.eval I) 0) t
    rw [hv0]
    exact hasDerivAt_const _ _
  exact p11cQ_flow_eq (p11cQ_field_slice_contDiffOn chi hI) hsol rfl 1 ⟨by norm_num, le_rfl⟩

/-- The slow part of `T w` only depends on the action and the slow part of `w`. -/
theorem p12c_slow_T (p : PlanarData) {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O)
    (w : Phase (2 + 2)) :
    p11cL_slow ((p11c_rotationLift p ∘ p11c_liftFlow chi.eval) w) =
      p11c_rotateSlow (p11c_frame p (p.axes (p11cL_act w)))
        (p11c_flow chi.eval (p11cL_act w) 1 (p11cL_slow w)) := by
  obtain ⟨c, hc⟩ := p11cB_T_assemble p chi.eval (p11cL_act w) (p11cL_slow w)
  have hw' : w = assemble (p11cL_act w) (p11cL_ang w) (p11cL_slow w).2 (p11cL_slow w).1 :=
    (p11cB_assemble_eta w).symm
  have h := hc (p11cL_ang w)
  rw [← hw'] at h
  rw [h]
  exact p11cL_slow_assemble _ _ _

private theorem continuous_assemble_zero :
    Continuous fun u : (Fin 2 → ℝ) × Phase 2 =>
      (assemble u.1 (0 : Fin 2 → ℝ) u.2.2 u.2.1 : Phase (2 + 2)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [Fin.append_left] <;>
      fun_prop
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [Fin.append_left] <;>
      fun_prop

private theorem continuous_slow_part :
    Continuous fun w : Phase (2 + 2) => p11cL_slow w := by
  unfold p11cL_slow
  fun_prop

private theorem slowLength_lt_of_norm {z : Phase 2} {s : ℝ} (hs : 0 < s) (hz : ‖z‖ ≤ s / 3) :
    p11c_slowLength z < s := by
  have h1 : ∀ i, |z.1 i| ≤ s / 3 := fun i =>
    ((norm_le_pi_norm z.1 i).trans (le_max_left _ _)).trans hz
  have h2 : ∀ i, |z.2 i| ≤ s / 3 := fun i =>
    ((norm_le_pi_norm z.2 i).trans (le_max_right _ _)).trans hz
  have hsq : ∀ x : ℝ, |x| ≤ s / 3 → x ^ 2 ≤ (s / 3) ^ 2 := fun x hx => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  unfold p11c_slowLength
  rw [sqrt_lt' hs, Fin.sum_univ_two]
  have := hsq _ (h1 0); have := hsq _ (h1 1); have := hsq _ (h2 0); have := hsq _ (h2 1)
  nlinarith

/-- Uniform smallness of the slow part of `T w` over a compact set of actions. -/
theorem p12c_slow_small (p : PlanarData) {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O)
    {rS : ℝ} (hrS : 0 < rS) {K0 : Set (Fin 2 → ℝ)} (hK0 : IsCompact K0) (hK0O : K0 ⊆ O)
    (hcont : ContinuousOn (p11c_rotationLift p ∘ p11c_liftFlow chi.eval) (p11c_tube O rS))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : Phase (2 + 2), p11cL_act w ∈ K0 → ‖p11cL_slow w‖ < ρ →
      ‖p11cL_slow ((p11c_rotationLift p ∘ p11c_liftFlow chi.eval) w)‖ < ε := by
  set T := p11c_rotationLift p ∘ p11c_liftFlow chi.eval with hT
  set K : Set ((Fin 2 → ℝ) × Phase 2) := K0 ×ˢ closedBall (0 : Phase 2) (rS / 3) with hK
  have hKc : IsCompact K := hK0.prod (isCompact_closedBall _ _)
  set f : (Fin 2 → ℝ) × Phase 2 → Phase 2 :=
    fun u => p11cL_slow (T (assemble u.1 (0 : Fin 2 → ℝ) u.2.2 u.2.1)) with hf
  have hfK : ContinuousOn f K := by
    refine (continuous_slow_part.comp_continuousOn (hcont.comp
      continuous_assemble_zero.continuousOn ?_))
    rintro ⟨I, z⟩ ⟨hI, hz⟩
    refine ⟨?_, ?_⟩
    · show p11cL_act (assemble I (0 : Fin 2 → ℝ) z.2 z.1) ∈ O
      rw [p11cL_act_assemble]; exact hK0O hI
    · show p11c_slowLength (p11cL_slow (assemble I (0 : Fin 2 → ℝ) z.2 z.1)) < rS
      rw [p11cL_slow_assemble]
      exact slowLength_lt_of_norm hrS (by simpa using hz)
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hfK) ε hε
  have hfS : ∀ u : (Fin 2 → ℝ) × Phase 2, f u =
      p11c_rotateSlow (p11c_frame p (p.axes u.1)) (p11c_flow chi.eval u.1 1 u.2) := by
    intro u
    simp only [hf, hT]
    rw [p12c_slow_T, p11cL_act_assemble, p11cL_slow_assemble]
  refine ⟨min δ (rS / 3), lt_min hδ (by positivity), fun w hw hlt => ?_⟩
  have hx : (p11cL_act w, p11cL_slow w) ∈ K :=
    ⟨hw, by simpa using (hlt.trans_le (min_le_right _ _)).le⟩
  have hy : (p11cL_act w, (0 : Phase 2)) ∈ K := ⟨hw, by simp; positivity⟩
  have hd : dist (p11cL_act w, p11cL_slow w) (p11cL_act w, (0 : Phase 2)) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    exact max_lt hδ (hlt.trans_le (min_le_left _ _))
  have h := hunif _ hx _ hy hd
  have hy0 : f (p11cL_act w, (0 : Phase 2)) = 0 := by
    rw [hfS]
    show p11c_rotateSlow _ (p11c_flow chi.eval (p11cL_act w) 1 0) = 0
    rw [p12c_flow_zero chi (hK0O hw)]
    simp [p11c_rotateSlow]
  rw [hy0, dist_zero_right] at h
  have hx0 : f (p11cL_act w, p11cL_slow w) = p11cL_slow (T w) := by
    rw [hfS, p12c_slow_T]
  rwa [hx0] at h

end KAM.Planetary

end
