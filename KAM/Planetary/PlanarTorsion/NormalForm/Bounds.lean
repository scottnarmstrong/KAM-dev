/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.QuarticFlow.Field
public import KAM.Planetary.PlanarTorsion.Characters

/-!
# Planar quartic torsion: uniform gradient bounds for quartic families (package T10)

Blueprint P, Part 11b (`bpP:p11b:lie`, `stepP:p11b:li-ord`).  The derivative of a quartic family
is homogeneous cubic, hence bounded by `C ‖w‖ ^ 3` uniformly on a compact parameter set
(`p11cN_grad_bound`); the difference of two families is a family (`p11cN_sub_family`) and the
torus average is a family (`p11cN_average_family`).  These give the degree `4 + 4 - 2 = 6`
estimates for the brackets in `lie`.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace KAM.Planetary

open KAM

/-- For a quartic family the `z`-derivative is the joint derivative composed with `inr`. -/
theorem p11cN_fderiv_slice {O : Set (Fin 2 → ℝ)} (G : QuarticFamily O) {I : Fin 2 → ℝ}
    (hI : I ∈ O) (w : Phase 2) :
    fderiv ℝ (G.eval I) w =
      (fderiv ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => G.eval u.1 u.2) (I, w)).comp
        (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Phase 2)) := by
  have hf := p11cQ_eval_analytic G (I, w) ⟨hI, mem_univ _⟩
  have h1 : HasFDerivAt (fun z : Phase 2 => ((I, z) : (Fin 2 → ℝ) × Phase 2))
      (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Phase 2)) w :=
    (hasFDerivAt_const I w).prodMk (hasFDerivAt_id w)
  exact ((hf.differentiableAt.hasFDerivAt (x := (I, w))).comp w h1).fderiv

/-- Uniform cubic bound of the derivative of a quartic family on a compact parameter set. -/
theorem p11cN_grad_bound {O : Set (Fin 2 → ℝ)} (G : QuarticFamily O) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 < C ∧ ∀ I ∈ K, ∀ w : Phase 2, ‖fderiv ℝ (G.eval I) w‖ ≤ C * ‖w‖ ^ 3 := by
  have hS : IsCompact (K ×ˢ (sphere (0 : Phase 2) 1)) := hK.prod (isCompact_sphere _ _)
  have hD : ContinuousOn (fun u : (Fin 2 → ℝ) × Phase 2 =>
      fderiv ℝ (fun v : (Fin 2 → ℝ) × Phase 2 => G.eval v.1 v.2) u) (O ×ˢ univ) :=
    (p11cQ_eval_analytic G).fderiv.continuousOn
  have hc : ContinuousOn (fun u : (Fin 2 → ℝ) × Phase 2 =>
      ‖fderiv ℝ (G.eval u.1) u.2‖) (K ×ˢ (sphere (0 : Phase 2) 1)) := by
    have h2 : ContinuousOn (fun u : (Fin 2 → ℝ) × Phase 2 =>
        (fderiv ℝ (fun v : (Fin 2 → ℝ) × Phase 2 => G.eval v.1 v.2) u).comp
          (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Phase 2))) (K ×ˢ (sphere (0 : Phase 2) 1)) :=
      (hD.mono fun u hu => ⟨hKO hu.1, mem_univ _⟩).clm_comp continuousOn_const
    refine (h2.norm).congr fun u hu => ?_
    rw [p11cN_fderiv_slice G (hKO hu.1)]
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun I hI w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    have h0 : fderiv ℝ (G.eval I) 0 = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      have := p11cQ_fderiv_smul G (hKO hI) (s := 2) two_ne_zero 0 v
      simp only [smul_zero] at this
      have h8 : (7 : ℝ) * fderiv ℝ (G.eval I) 0 v = 0 := by
        have : (2 : ℝ) ^ 3 * fderiv ℝ (G.eval I) 0 v - fderiv ℝ (G.eval I) 0 v = 0 := by
          rw [← this]; ring
        linarith
      have := (mul_eq_zero.1 h8).resolve_left (by norm_num)
      simpa using this
    simp [h0]
  · have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hu : ‖w‖⁻¹ • w ∈ sphere (0 : Phase 2) 1 := by
      simp [norm_smul, hn.ne']
    have hsm : fderiv ℝ (G.eval I) w = ‖w‖ ^ 3 • fderiv ℝ (G.eval I) (‖w‖⁻¹ • w) := by
      refine ContinuousLinearMap.ext fun v => ?_
      have := p11cQ_fderiv_smul G (hKO hI) (s := ‖w‖) hn.ne' (‖w‖⁻¹ • w) v
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at this
      simpa using this
    rw [hsm, norm_smul, norm_pow, norm_norm]
    have hb := hB (I, ‖w‖⁻¹ • w) ⟨hI, hu⟩
    simp only [Real.norm_eq_abs, abs_norm] at hb
    calc ‖w‖ ^ 3 * ‖fderiv ℝ (G.eval I) (‖w‖⁻¹ • w)‖
        ≤ ‖w‖ ^ 3 * max B 1 := by gcongr; exact hb.trans (le_max_left _ _)
      _ = max B 1 * ‖w‖ ^ 3 := by ring

/-- The difference of two quartic families is a quartic family. -/
theorem p11cN_sub_family {O : Set (Fin 2 → ℝ)} (F A : QuarticFamily O) :
    ∃ D : QuarticFamily O, ∀ I z, D.eval I z = F.eval I z - A.eval I z := by
  refine ⟨⟨fun a I => F.coeff a I - A.coeff a I, fun a => (F.analytic a).sub (A.analytic a)⟩, ?_⟩
  intro I z
  unfold QuarticFamily.eval
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The torus average of a quartic family is a quartic family (on `O`). -/
theorem p11cN_average_family {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) :
    ∃ A : QuarticFamily O, ∀ I ∈ O, ∀ z, A.eval I z = p11c_average F.eval I z := by
  obtain ⟨a, b, c, ha, hb, hc, hav⟩ := average_action_polynomial F
  obtain ⟨A, hA⟩ := quartic_of_actions ha hb hc
  exact ⟨A, fun I hI z => by rw [hA, hav I hI z]⟩

end KAM.Planetary

end
