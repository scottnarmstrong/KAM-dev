/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.OrbitComplex
public import KAM.Kepler.DelaunaySymplectic
public import KAM.Iso.ComplexDomain

/-!
# Literal exports for the Delaunay orbit-map and symplectic steps (GAP-I7a)

Unsigned exports stating the literal conclusions of `stepI:p7:om-hol`, `stepI:p7:sy-ext` and
`stepI:p7:sy-field` from the landed declarations of `KAM.Kepler.OrbitComplex`,
`KAM.Kepler.KeplerTube` and `KAM.Kepler.DelaunaySymplectic`.

* `orbitStep_om_hol`: holomorphy of `u, cos u, sin u`, the bound `‖1 - e cos u‖ ≥ 1 - ϑ* > 0`,
  holomorphy of `Q_el`, the tube bound `‖e‖ ≤ e₂ < 1` and holomorphy of `k = √(1 - e²)`;
* `delaunayStep_sy_ext`: symplecticity in the form language of `cv-sympl`
  (`IsSymplecticOn 1`, the frozen form is the matrix `𝕁`), invertibility (`det ≠ 0`) and the
  dual identity `D𝒬 𝕁 D𝒬ᵀ = 𝕁`, stated as symplecticity of the inverse;
* `delaunayStep_sy_field`: `D𝒬 X_{H∘𝒬} = X_H ∘ 𝒬` and the curve equivalence.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Kepler

open KAM KAM.Planetary

/-- `stepI:p7:om-hol`: holomorphy of `u, cos u, sin u`; `|𝖣| ≥ 1 - ϑ* > 0`; holomorphy of `𝖰_el`;
`|e| ≤ e₂ < 1` on the tube and `Re (1 - e²) > 0`; holomorphy of `k = √(1 - e²)`. -/
theorem orbitStep_om_hol {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) :
    DifferentiableOn ℂ (fun x : Fin 5 → ℂ => eccAnomC e₁ (x 0, x 3)) (orbitDomC e₁) ∧
    DifferentiableOn ℂ (fun x : Fin 5 → ℂ => Complex.cos (eccAnomC e₁ (x 0, x 3)))
      (orbitDomC e₁) ∧
    DifferentiableOn ℂ (fun x : Fin 5 → ℂ => Complex.sin (eccAnomC e₁ (x 0, x 3)))
      (orbitDomC e₁) ∧
    0 < 1 - keplerTheta e₁ ∧
    (∀ x ∈ orbitDomC e₁,
      1 - keplerTheta e₁ ≤ ‖1 - x 3 * Complex.cos (eccAnomC e₁ (x 0, x 3))‖) ∧
    DifferentiableOn ℂ (orbitMapC e₁) (orbitDomC e₁) ∧
    (∀ x ∈ orbitDomC e₁, ‖x 3‖ ≤ keplerE2 e₁) ∧ keplerE2 e₁ < 1 ∧
    (∀ x ∈ orbitDomC e₁, 0 < (1 - x 3 ^ 2).re) ∧
    DifferentiableOn ℂ (fun x : Fin 5 → ℂ => (1 - x 3 ^ 2) ^ (1 / 2 : ℂ)) (orbitDomC e₁) := by
  have hu := OrbitC.differentiableOn_u h0 h1
  have hc := keplerConstants_pos h0 h1
  have he2 : ∀ x ∈ orbitDomC e₁, ‖x 3‖ ≤ keplerE2 e₁ := fun x hx =>
    (Tube.tube_bounds h0 hx.1).1
  have e2lt : keplerE2 e₁ < 1 := by unfold keplerE2; linarith
  have hre : ∀ x ∈ orbitDomC e₁, 0 < (1 - x 3 ^ 2).re := by
    intro x hx
    have h2 : ‖x 3‖ ≤ keplerE2 e₁ := he2 x hx
    have h3 : ‖x 3 ^ 2‖ ≤ keplerE2 e₁ ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 := Complex.re_le_norm (x 3 ^ 2)
    have h5 : 0 ≤ keplerE2 e₁ := (Tube.e2_pos h0).le
    have h6 : (1 - x 3 ^ 2).re = 1 - (x 3 ^ 2).re := by simp
    rw [h6]
    nlinarith
  refine ⟨hu, hu.ccos, hu.csin, by linarith [hc.2.2.2.2.2],
    fun x hx => ((keplerEq_tube h0 h1).2.2.2 (x 0, x 3) hx.1).2.2.2,
    orbitMapC_differentiableOn h0 h1, he2, e2lt, hre, ?_⟩
  have hd : DifferentiableOn ℂ (fun x : Fin 5 → ℂ => 1 - x 3 ^ 2) (orbitDomC e₁) := by
    fun_prop
  exact hd.cpow_const fun x hx => KAM.Iso.ComplexDomainAux.slit_of_re_pos (hre x hx)

/-- `stepI:p7:sy-ext`, in the form language of `cv-sympl` (`IsSymplecticOn 1` is `DQᵀ𝕁DQ = 𝕁`
for the frozen form): `Ω(DQ u, DQ v) = Ω(u, v)` on `deDom`; `DQ` is invertible with
`det ≠ 0`; and the dual identity `DQ 𝕁 DQᵀ = 𝕁`, equivalently `Ω(DQ⁻¹ u, DQ⁻¹ v) = Ω(u, v)`. -/
theorem delaunayStep_sy_ext :
    IsSymplecticOn 1 delaunay deDom ∧
    ∀ w ∈ deDom, ∃ A : Phase 2 ≃L[ℝ] Phase 2, (A : Phase 2 →L[ℝ] Phase 2) = fderiv ℝ delaunay w ∧
      LinearMap.det (A : Phase 2 →ₗ[ℝ] Phase 2) ≠ 0 ∧
      ∀ u v : Phase 2, symplecticForm (A.symm u) (A.symm v) = symplecticForm u v := by
  refine ⟨delaunay_symplectic, fun w hw => ?_⟩
  obtain ⟨A, hA⟩ := delaunay_fderiv_equiv hw
  refine ⟨A, hA, ?_, fun u v => ?_⟩
  · have : LinearMap.det (A.toLinearEquiv : Phase 2 →ₗ[ℝ] Phase 2) ≠ 0 :=
      (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
    exact this
  · have h := delaunay_symplectic w hw (A.symm u) (A.symm v)
    rw [one_mul, ← hA] at h
    simpa using h.symm

/-- `stepI:p7:sy-field`: on `W = {w ∈ deDom : 𝒬 w ∈ U}`, `D𝒬 X_{H∘𝒬} = X_H ∘ 𝒬`, and for a curve
`w` differentiable at `t` with `w t ∈ W`, `w' = X_{H∘𝒬}(w)` iff `(𝒬 ∘ w)' = X_H(𝒬 w)`. -/
theorem delaunayStep_sy_field {U : Set (Phase 2)} (hU : IsOpen U) {H : Phase 2 → ℝ}
    (hH : ContDiffOn ℝ 1 H U) :
    (∀ w ∈ deDom, delaunay w ∈ U →
      fderiv ℝ delaunay w (hamiltonianVectorField (H ∘ delaunay) w) =
        hamiltonianVectorField H (delaunay w)) ∧
    ∀ (w : ℝ → Phase 2) (t : ℝ), DifferentiableAt ℝ w t → w t ∈ deDom → delaunay (w t) ∈ U →
      (HasDerivAt w (hamiltonianVectorField (H ∘ delaunay) (w t)) t ↔
        HasDerivAt (fun s => delaunay (w s)) (hamiltonianVectorField H (delaunay (w t))) t) := by
  have hdiff : ∀ w ∈ deDom, delaunay w ∈ U → DifferentiableAt ℝ H (delaunay w) := fun w _ hwU =>
    ((hH.contDiffAt (hU.mem_nhds hwU)).differentiableAt (by norm_num))
  refine ⟨fun w hw hwU => delaunay_hamiltonianVectorField hw (hdiff w hw hwU),
    fun w t hwt hw hwU => ?_⟩
  have hQ : HasFDerivAt delaunay (fderiv ℝ delaunay (w t)) (w t) := delaunay_hasFDerivAt hw
  have hX := delaunay_hamiltonianVectorField hw (hdiff _ hw hwU)
  constructor
  · intro h
    have := hQ.comp_hasDerivAt t h
    rwa [hX] at this
  · intro h
    obtain ⟨A, hA⟩ := delaunay_fderiv_equiv hw
    have h1 := hQ.comp_hasDerivAt t hwt.hasDerivAt
    have h2 := h1.unique (hX ▸ h : HasDerivAt (fun s => delaunay (w s))
      (fderiv ℝ delaunay (w t) (hamiltonianVectorField (H ∘ delaunay) (w t))) t)
    have hinj : Function.Injective (fderiv ℝ delaunay (w t)) := by
      rw [← hA]; exact A.injective
    have := hinj h2
    rw [← this]
    exact hwt.hasDerivAt
end KAM.Kepler

end
