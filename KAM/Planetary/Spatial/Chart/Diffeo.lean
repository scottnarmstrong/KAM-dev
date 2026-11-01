/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Chart.Symplectic

/-!
# The regular spatial Poincare chart is a local analytic diffeomorphism

Package LP-SP-CHART, `LP:MAIN L17 (571–578)`, track LP, non-frozen. Items 3–5: a symplectic
map has an injective, hence (finite dimension) invertible, derivative. With analyticity this
gives, at every point of (44), an open partial homeomorphism extending `spatialPoincare ν` whose
inverse is analytic, as for the planar chart (`poincare_localDiffeo`).
-/

@[expose] public noncomputable section

open Matrix

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

variable {ν : ℝ} {w : Phase 3}

/-- Nondegeneracy of `symplecticForm` on `Phase 3`. -/
lemma eq_zero_of_symplecticForm_eq_zero (u : Phase 3) (h : ∀ v : Phase 3, symplecticForm u v = 0) :
    u = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := h (0, Pi.single i 1)
    simpa [symplecticForm, Pi.single_apply] using this
  · have := h (Pi.single i 1, 0)
    simpa [symplecticForm, Pi.single_apply] using this

/-- The derivative of the spatial chart is a linear equivalence on (44). -/
theorem spatialPoincare_fderiv_equiv (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    ∃ A : Phase 3 ≃L[ℝ] Phase 3, (A : Phase 3 →L[ℝ] Phase 3) = fderiv ℝ (spatialPoincare ν) w := by
  set L := fderiv ℝ (spatialPoincare ν) w with hL
  have hker : LinearMap.ker (L : Phase 3 →ₗ[ℝ] Phase 3) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    refine eq_zero_of_symplecticForm_eq_zero u fun v => ?_
    have h1 := spatialPoincare_symplectic_at hν hw u v
    have hu' : L u = 0 := hu
    rw [← h1, hL] at *
    rw [hu']
    simp [symplecticForm]
  have hinj : Function.Injective (L : Phase 3 →ₗ[ℝ] Phase 3) := LinearMap.ker_eq_bot.1 hker
  have hsurj : Function.Surjective (L : Phase 3 →ₗ[ℝ] Phase 3) :=
    LinearMap.injective_iff_surjective.1 hinj
  refine ⟨ContinuousLinearEquiv.ofBijective L hker ?_, ?_⟩
  · exact LinearMap.range_eq_top.2 hsurj
  · exact ContinuousLinearMap.ext fun z => rfl

/-- Items 3–5: a local analytic diffeomorphism extending `spatialPoincare ν` at every point of (44). -/
theorem spatialPoincare_localDiffeo (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) :
    ∃ φ : OpenPartialHomeomorph (Phase 3) (Phase 3), w ∈ φ.source ∧
      (φ : Phase 3 → Phase 3) = spatialPoincare ν ∧ AnalyticOnNhd ℝ φ.symm φ.target := by
  have hana := analyticOnNhd_spatialPoincare hν
  obtain ⟨A, hA⟩ := spatialPoincare_fderiv_equiv hν hw
  have hc : ContDiffAt ℝ ω (spatialPoincare ν) w := (hana w hw).contDiffAt
  have hf' : HasFDerivAt (spatialPoincare ν) (A : Phase 3 →L[ℝ] Phase 3) w := by
    rw [hA]; exact (hana w hw).differentiableAt.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let φ0 := hc.toOpenPartialHomeomorph (spatialPoincare ν) hf' hn
  let φ := φ0.restrOpen spatialPoincareDom isOpen_spatialPoincareDom
  have hcoe : (φ : Phase 3 → Phase 3) = spatialPoincare ν := rfl
  refine ⟨φ, ⟨hc.mem_toOpenPartialHomeomorph_source hf' hn, hw⟩, hcoe, ?_⟩
  intro y hy
  have hxs : φ.symm y ∈ φ.source := φ.map_target hy
  have hx : φ.symm y ∈ spatialPoincareDom := hxs.2
  obtain ⟨B, hB⟩ := spatialPoincare_fderiv_equiv hν hx
  have hB' : HasFDerivAt φ (B : Phase 3 →L[ℝ] Phase 3) (φ.symm y) := by
    rw [hcoe, hB]
    exact (hana _ hx).differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℝ ω φ (φ.symm y) := by
    rw [hcoe]; exact (hana _ hx).contDiffAt
  exact (φ.contDiffAt_symm hy hB' hcd).analyticAt

end KAM.Planetary.Spatial
