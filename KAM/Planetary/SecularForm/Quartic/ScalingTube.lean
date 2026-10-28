/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.ScalingComplex
public import KAM.Planetary.SecularForm.ParameterIntegral

/-!
# Secular form: uniform branch conditions and the holomorphic cell integral

Blueprint P, Part 8, `stepP:p8:q4-a`: around the complexified real parameters of a point of
`separatedDomain` all branch conditions hold uniformly in the angles (tube lemma), so the
normalised cell integral of the complexified integrand is holomorphic there (`e_param`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- The normalised cell integral of the complexified integrand. -/
def qscAvgC (ζ : Fin 5 → ℂ) : ℂ :=
  ((2 * π) ^ (-((2 : ℕ) : ℤ))) • ∫ t in cell 2, qscIntC ζ (t 0) (t 1)

theorem qsc_tube {z₀ : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hz : z₀ ∈ separatedDomain) :
    ∃ U : Set (Fin 5 → ℂ), IsOpen U ∧ qscEmb z₀ ∈ U ∧
      ∀ ζ ∈ U, ∀ F₁ ∈ Icc (0:ℝ) (2 * π), ∀ F₂ ∈ Icc (0:ℝ) (2 * π), qscGood ζ F₁ F₂ := by
  obtain ⟨c1, c2, c3, c4, -⟩ := qsc_good_real hz 0 0
  set ζ₀ := qscEmb z₀ with hζ₀
  have n1 : ∀ᶠ ζ in 𝓝 ζ₀, 1 - ζ 1 ^ 2 - ζ 2 ^ 2 ∈ Complex.slitPlane :=
    (Continuous.continuousAt (by fun_prop)).eventually (Complex.isOpen_slitPlane.mem_nhds c1)
  have n2 : ∀ᶠ ζ in 𝓝 ζ₀, 1 - ζ 3 ^ 2 - ζ 4 ^ 2 ∈ Complex.slitPlane :=
    (Continuous.continuousAt (by fun_prop)).eventually (Complex.isOpen_slitPlane.mem_nhds c2)
  have k1 : ContinuousAt (fun ζ : Fin 5 → ℂ => qscKC (ζ 1) (ζ 2)) ζ₀ :=
    (qsc_contAt_kC c1).comp (f := fun ζ : Fin 5 → ℂ => (ζ 1, ζ 2)) (by fun_prop)
  have k2 : ContinuousAt (fun ζ : Fin 5 → ℂ => qscKC (ζ 3) (ζ 4)) ζ₀ :=
    (qsc_contAt_kC c2).comp (f := fun ζ : Fin 5 → ℂ => (ζ 3, ζ 4)) (by fun_prop)
  have n3 : ∀ᶠ ζ in 𝓝 ζ₀, 1 + qscKC (ζ 1) (ζ 2) ≠ 0 :=
    (continuousAt_const.add k1).eventually_ne c3
  have n4 : ∀ᶠ ζ in 𝓝 ζ₀, 1 + qscKC (ζ 3) (ζ 4) ≠ 0 :=
    (continuousAt_const.add k2).eventually_ne c4
  have n5 : ∀ᶠ ζ in 𝓝 ζ₀, ∀ F ∈ Icc (0:ℝ) (2 * π) ×ˢ Icc (0:ℝ) (2 * π),
      qscSep ζ F.1 F.2 ∈ Complex.slitPlane := by
    refine (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
      (P := fun ζ F => qscSep ζ F.1 F.2 ∈ Complex.slitPlane) fun F _ => ?_
    have hc := qsc_contAt_sep (F₁ := F.1) (F₂ := F.2) c1 c2 c3 c4
    have hv := (qsc_good_real hz F.1 F.2).2.2.2.2
    exact hc.eventually (Complex.isOpen_slitPlane.mem_nhds hv)
  obtain ⟨U, hU, hUo, hU0⟩ := eventually_nhds_iff.1 (n1.and (n2.and (n3.and (n4.and n5))))
  refine ⟨U, hUo, hU0, fun ζ hζ F₁ h₁ F₂ h₂ => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := hU ζ hζ
  exact ⟨a1, a2, a3, a4, a5 (F₁, F₂) ⟨h₁, h₂⟩⟩

theorem qsc_differentiableOn {U : Set (Fin 5 → ℂ)} (hU : IsOpen U)
    (hg : ∀ ζ ∈ U, ∀ F₁ ∈ Icc (0:ℝ) (2 * π), ∀ F₂ ∈ Icc (0:ℝ) (2 * π), qscGood ζ F₁ F₂) :
    DifferentiableOn ℂ qscAvgC U := by
  have hcell : ∀ t ∈ cell 2, t 0 ∈ Icc (0:ℝ) (2 * π) ∧ t 1 ∈ Icc (0:ℝ) (2 * π) :=
    fun t ht => ⟨Set.mem_pi.1 ht 0 (mem_univ _), Set.mem_pi.1 ht 1 (mem_univ _)⟩
  have hcont : ContinuousOn (fun z : Vec 2 × (Fin 5 → ℂ) => qscIntC z.2 (z.1 0) (z.1 1))
      (cell 2 ×ˢ U) := by
    intro z hz
    obtain ⟨h0, h1⟩ := hcell z.1 hz.1
    have := qsc_contAt_KC (hg z.2 hz.2 _ h0 _ h1)
    exact (this.comp (f := fun z : Vec 2 × (Fin 5 → ℂ) => (z.2, z.1 0, z.1 1))
      (x := z) (by fun_prop)).continuousWithinAt
  have hhol : ∀ t ∈ cell 2, DifferentiableOn ℂ (fun ζ => qscIntC ζ (t 0) (t 1)) U := by
    intro t ht ζ hζ
    obtain ⟨h0, h1⟩ := hcell t ht
    exact (qsc_diffAt_KC _ _ (hg ζ hζ _ h0 _ h1)).differentiableWithinAt
  exact (e_param hU (f := fun t ζ => qscIntC ζ (t 0) (t 1)) hcont hhol).const_smul (((2 * π) ^ (-((2 : ℕ) : ℤ)) : ℝ))

theorem qsc_avgC_real {y : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hy : y ∈ separatedDomain) :
    qscAvgC (qscEmb y) = ((avg (fun t : Vec 2 => qscG y (t 0) (t 1)) : ℝ) : ℂ) := by
  unfold qscAvgC avg
  simp only [qsc_intC_real hy]
  rw [integral_complex_ofReal, Complex.real_smul, smul_eq_mul]
  push_cast
  rfl

end SecularForm
end KAM.Planetary
end
