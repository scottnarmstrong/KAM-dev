/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Defs
public import KAM.ODE.Basic

/-!
# Planar quartic torsion: the real Lie-Taylor formula (package T10)

Blueprint P, Part 11b (`bpP:p11b:lie`, `stepP:p11b:li-tay`).  Along an actual solution `g` of the
Hamiltonian field of `chi` in an open set `U`, an analytic `K` satisfies the chain rule
`(K ∘ g)' = {K, chi} ∘ g` and the order-two integral Taylor formula `real_lie_taylor`.  No
complex smallness hypothesis is used.
-/

@[expose] public noncomputable section

open Set Metric Function MeasureTheory
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.ODE

/-- Application of an analytic family of continuous linear maps to an analytic vector. -/
theorem p11cN_clm_apply {z : Phase 2} {A : Phase 2 → (Phase 2 →L[ℝ] ℝ)} {v : Phase 2 → Phase 2}
    (hA : AnalyticAt ℝ A z) (hv : AnalyticAt ℝ v z) : AnalyticAt ℝ (fun w => A w (v w)) z :=
  ((ContinuousLinearMap.apply ℝ ℝ : Phase 2 →L[ℝ] (Phase 2 →L[ℝ] ℝ) →L[ℝ] ℝ).analyticAt_bilinear
      (v z, A z)).comp
    (f := fun w => (v w, A w)) (hv.prod hA)

/-- The Hamiltonian vector field of an analytic function is analytic. -/
theorem p11cN_field_analytic {U : Set (Phase 2)} {chi : Phase 2 → ℝ}
    (hc : AnalyticOnNhd ℝ chi U) : AnalyticOnNhd ℝ (hamiltonianVectorField chi) U := by
  intro z hz
  have h1 : ∀ v : Phase 2, AnalyticAt ℝ (fun z => fderiv ℝ chi z v) z :=
    fun v => p11cN_clm_apply (hc.fderiv z hz) analyticAt_const
  unfold hamiltonianVectorField
  refine AnalyticAt.prod ?_ ?_
  · exact analyticAt_pi_iff.2 fun i => h1 _
  · exact analyticAt_pi_iff.2 fun i => (h1 _).neg

/-- The Poisson bracket of analytic functions is analytic. -/
theorem p11cN_bracket_analytic {U : Set (Phase 2)} {K chi : Phase 2 → ℝ}
    (hK : AnalyticOnNhd ℝ K U) (hc : AnalyticOnNhd ℝ chi U) :
    AnalyticOnNhd ℝ (p11c_bracket K chi) U := fun z hz =>
  p11cN_clm_apply (hK.fderiv z hz) (p11cN_field_analytic hc z hz)

/-- Chain rule along a solution: `(f ∘ g)' = {f, chi} ∘ g`. -/
theorem p11cN_hasDerivAt {U : Set (Phase 2)} {f chi : Phase 2 → ℝ}
    (hf : AnalyticOnNhd ℝ f U) {J : Set ℝ} {g : ℝ → Phase 2}
    (hg : IsSolutionIn (hamiltonianVectorField chi) U J g) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s => f (g s)) (p11c_bracket f chi (g t)) t := by
  obtain ⟨hgU, hgd⟩ := hg t ht
  have hfd : DifferentiableAt ℝ f (g t) := (hf _ hgU).differentiableAt
  exact hfd.hasFDerivAt.comp_hasDerivAt t hgd

/-- Real chain-rule and order-two integral Taylor formula on a supplied actual solution. -/
theorem real_lie_taylor {U : Set (Phase 2)} (hU : IsOpen U) (K chi : Phase 2 → ℝ)
    (hK : AnalyticOnNhd ℝ K U) (hc : AnalyticOnNhd ℝ chi U)
    (g : ℝ → Phase 2) (hg : IsSolutionIn (hamiltonianVectorField chi) U (Icc (0 : ℝ) 1) g) :
    K (g 1) = K (g 0) + p11c_bracket K chi (g 0) +
      ∫ t in (0 : ℝ)..1, (1 - t) * p11c_bracket (p11c_bracket K chi) chi (g t) := by
  have hB := p11cN_bracket_analytic hK hc
  have hB2 := p11cN_bracket_analytic hB hc
  have h1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => K (g s)) (p11c_bracket K chi (g t)) t :=
    fun t ht => p11cN_hasDerivAt hK hg ht
  have h2 : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => p11c_bracket K chi (g s))
        (p11c_bracket (p11c_bracket K chi) chi (g t)) t :=
    fun t ht => p11cN_hasDerivAt hB hg ht
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := fun t ht => (hg t ht).2.continuousAt.continuousWithinAt
  have hmaps : MapsTo g (Icc (0 : ℝ) 1) U := fun t ht => (hg t ht).1
  have hi1 : IntervalIntegrable (fun t => p11c_bracket K chi (g t)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (hB.continuousOn.comp hgc hmaps).integrableOn_Icc
  have hi2 : IntervalIntegrable (fun t => p11c_bracket (p11c_bracket K chi) chi (g t))
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (hB2.continuousOn.comp hgc hmaps).integrableOn_Icc
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => 1 - t) (-1) x := fun x _ => by
    simpa using (hasDerivAt_id x).const_sub 1
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu
    (v := fun s => p11c_bracket K chi (g s))
    (fun x hx => h2 x (by simpa [uIcc_of_le zero_le_one] using hx))
    (by simp) hi2
  have hfund : ∫ t in (0 : ℝ)..1, p11c_bracket K chi (g t) = K (g 1) - K (g 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => h1 x (by simpa [uIcc_of_le zero_le_one] using hx)) hi1
  have hneg : ∫ t in (0 : ℝ)..1, (-1 : ℝ) * p11c_bracket K chi (g t) =
      -(K (g 1) - K (g 0)) := by
    rw [intervalIntegral.integral_const_mul, hfund]; ring
  rw [hparts, hneg]
  simp
  ring

end KAM.Planetary

end
