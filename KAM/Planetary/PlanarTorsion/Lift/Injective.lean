/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Lift.Inverse

/-!
# Planar quartic torsion: the lift of `-chi` inverts the lift of `chi` (package T11)

Blueprint P, Part 11b (`bpP:p11b:lm-prop`, injectivity).  On the tube the lift of `-chi` is a left
inverse of the lift of `chi`: the action is constant, the slow part is inverted by the last clause
of the signed theorem `flow`, the backward trajectory of `-chi` is the time-reversed trajectory of
`chi` (ODE uniqueness), and the angle integral `∫ ∂_I chi` is odd under time reversal.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

variable {O O' : Set (Fin 2 → ℝ)}

/-- The negated quartic family. -/
def p11cL_negFamily (chi : QuarticFamily O) : QuarticFamily O :=
  ⟨fun a I => -chi.coeff a I, fun a => (chi.analytic a).neg⟩

theorem p11cL_negFamily_eval (chi : QuarticFamily O) :
    (p11cL_negFamily chi).eval = fun J w => -chi.eval J w := by
  funext J w
  simp [QuarticFamily.eval, p11cL_negFamily, Finset.sum_neg_distrib]

/-- The backward trajectory of `-chi` from the end point is the reversed trajectory of `chi`. -/
theorem p11cL_reverse (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)} (hKO : K ⊆ O) {R : ℝ}
    (hfs : p11cL_FlowSpec chi.eval K R)
    (hfsn : p11cL_FlowSpec (fun J w => -chi.eval J w) K R) {I : Fin 2 → ℝ} (hI : I ∈ K)
    {z : Phase 2} (hz : p11c_slowLength z < R)
    (hZ : p11c_slowLength (p11c_flow chi.eval I 1 z) < R) :
    ∀ s ∈ Icc (0 : ℝ) 1, p11c_flow (fun J w => -chi.eval J w) I s (p11c_flow chi.eval I 1 z) =
      p11c_flow chi.eval I (1 - s) z := by
  obtain ⟨h0, hsol, -⟩ := hfs I hI z hz
  obtain ⟨h0', hsol', -⟩ := hfsn I hI _ hZ
  have hF1 := p11cQ_field_slice_contDiffOn chi (hKO hI)
  have hF1' : ContDiffOn ℝ 1 (hamiltonianVectorField ((fun J w => -chi.eval J w) I)) univ := by
    show ContDiffOn ℝ 1 (hamiltonianVectorField (fun w => -chi.eval I w)) univ
    rw [p11cQ_ham_neg]; exact hF1.neg
  have hH : IsSolutionIn (hamiltonianVectorField ((fun J w => -chi.eval J w) I)) univ (Icc 0 1)
      (fun s => p11c_flow chi.eval I (1 - s) z) := by
    intro s hs'
    refine ⟨mem_univ _, ?_⟩
    have := (hsol (1 - s) ⟨by linarith [hs'.2], by linarith [hs'.1]⟩).2.comp_const_sub 1 s
    show HasDerivAt _ (hamiltonianVectorField (fun w => -chi.eval I w) _) s
    rw [p11cQ_ham_neg]
    simpa using this
  intro s hs
  exact gen_uniqueness isOpen_univ hF1' ordConnected_Icc (t₀ := 0) ⟨le_rfl, zero_le_one⟩
    (hsol'.mono (Icc_subset_Icc (by norm_num) le_rfl)) hH (by simp [h0']) hs

/-- The lift of `-chi` is a left inverse of the lift of `chi` on the tube. -/
theorem p11cL_left_inverse (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)} (hKO : K ⊆ O)
    {r : ℝ} (hr : 0 < r) (hO'K : O' ⊆ K) (hfs : p11cL_FlowSpec chi.eval K (2 * r))
    (hfsn : p11cL_FlowSpec (fun J w => -chi.eval J w) K (2 * r))
    (hinv : ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < 2 * r →
      p11c_flow (fun J w => -chi.eval J w) I 1 (p11c_flow chi.eval I 1 z) = z)
    {w : Phase (2 + 2)} (hw : w ∈ p11c_tube O' r) :
    p11c_liftFlow (fun J w => -chi.eval J w) (p11c_liftFlow chi.eval w) = w := by
  obtain ⟨hIO', hz⟩ := hw
  replace hz : p11c_slowLength (p11cL_slow w) < r := hz
  have hIK : p11cL_act w ∈ K := hO'K hIO'
  have hz2 : p11c_slowLength (p11cL_slow w) < 2 * r := by linarith
  have hZ : p11c_slowLength (p11c_flow chi.eval (p11cL_act w) 1 (p11cL_slow w)) < 2 * r := by
    obtain ⟨-, -, hen⟩ := hfs _ hIK _ hz2
    have h1 := hen 1 ⟨by norm_num, le_rfl⟩
    have h0 : (0 : ℝ) ≤ p11c_slowLength (p11cL_slow w) := Real.sqrt_nonneg _
    by_contra hc
    push_neg at hc
    nlinarith [mul_self_lt_mul_self h0 hz]
  have hrev := p11cL_reverse chi hKO hfs hfsn hIK hz2 hZ
  obtain ⟨h0, -, -⟩ := hfs _ hIK _ hz2
  set Y := p11c_flow chi.eval (p11cL_act w) 1 (p11cL_slow w) with hY
  set g : Fin 2 → ℝ := fun i => ∫ t in (0 : ℝ)..1,
    fderiv ℝ (fun J => chi.eval J (p11c_flow chi.eval (p11cL_act w) t (p11cL_slow w)))
      (p11cL_act w) (Pi.single i 1) with hg
  have hw' : p11c_liftFlow chi.eval w =
      assemble (p11cL_act w) (p11cL_ang w + g) Y.2 Y.1 := p11cL_liftFlow_eq _ w
  rw [p11cL_liftFlow_eq, hw', p11cL_act_assemble, p11cL_ang_assemble, p11cL_slow_assemble]
  have hinv' := hinv _ hIK _ hz2
  have hint : (fun i => ∫ t in (0 : ℝ)..1, fderiv ℝ
      (fun J => (fun J w => -chi.eval J w) J (p11c_flow (fun J w => -chi.eval J w)
        (p11cL_act w) t Y)) (p11cL_act w) (Pi.single i 1)) = -g := by
    funext i
    have h1 : ∀ t ∈ uIcc (0 : ℝ) 1, fderiv ℝ (fun J => (fun J w => -chi.eval J w) J
        (p11c_flow (fun J w => -chi.eval J w) (p11cL_act w) t Y)) (p11cL_act w) (Pi.single i 1) =
        -(fun s => fderiv ℝ (fun J => chi.eval J (p11c_flow chi.eval (p11cL_act w) s
          (p11cL_slow w))) (p11cL_act w) (Pi.single i 1)) (1 - t) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [hrev t ht]
      rw [fderiv_fun_neg]
      rfl
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_sub_left
        (fun s => fderiv ℝ (fun J => chi.eval J (p11c_flow chi.eval (p11cL_act w) s
          (p11cL_slow w))) (p11cL_act w) (Pi.single i 1)) 1]
    simp [hg]
  rw [hint, hinv']
  have : p11cL_ang w + g + -g = p11cL_ang w := by abel
  rw [this]
  exact p11cL_assemble_eq w

theorem p11cL_injOn (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)} (hKO : K ⊆ O)
    {r : ℝ} (hr : 0 < r) (hO'K : O' ⊆ K) (hfs : p11cL_FlowSpec chi.eval K (2 * r))
    (hfsn : p11cL_FlowSpec (fun J w => -chi.eval J w) K (2 * r))
    (hinv : ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < 2 * r →
      p11c_flow (fun J w => -chi.eval J w) I 1 (p11c_flow chi.eval I 1 z) = z) :
    InjOn (p11c_liftFlow chi.eval) (p11c_tube O' r) := fun w₁ h₁ w₂ h₂ h => by
  rw [← p11cL_left_inverse chi hKO hr hO'K hfs hfsn hinv h₁,
    ← p11cL_left_inverse chi hKO hr hO'K hfs hfsn hinv h₂, h]

end KAM.Planetary

end
