/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.FastShift
public import KAM.Kepler.Basic
public import KAM.ODE.Basic
public import KAM.Planetary.Hamiltonian.Algebra

/-!
# Symplectic charts on `Phase d`

`bpP:p1:chart`, `chart-field`, `chart-orbit`, `typical` (2),(3), `period-convert` (a),(b),(d) and
`stepP:p1:li-det`. A `c`-chart is an analytic map with `Ω(DΨ u, DΨ v) = c Ω(u, v)` on `O`; the field
identity `DΨ X_{H^Ψ} = X_H ∘ Ψ` is proved through the inverse function theorem. This module owns
`angleScale` (`S_c`) and `fullShift`.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

section Chart

variable {d : ℕ}

/-- `bpP:p1:chart`: `Ψ` is a `c`-chart on `O` (openness of `O` and `0 < c` are separate hypotheses
at use sites). Unfolds to `AnalyticOnNhd` + the Kepler design's `IsSymplecticOn`. -/
def IsChart (c : ℝ) (Ψ : Phase d → Phase d) (O : Set (Phase d)) : Prop :=
  AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O

theorem isChart_iff {c : ℝ} {Ψ : Phase d → Phase d} {O : Set (Phase d)} :
    IsChart c Ψ O ↔ AnalyticOnNhd ℝ Ψ O ∧ IsSymplecticOn c Ψ O := Iff.rfl

theorem IsChart.analyticOnNhd {c : ℝ} {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) : AnalyticOnNhd ℝ Ψ O := h.1

theorem IsChart.symplectic {c : ℝ} {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) : IsSymplecticOn c Ψ O := h.2

theorem IsChart.mono {c : ℝ} {Ψ : Phase d → Phase d} {O O' : Set (Phase d)}
    (h : IsChart c Ψ O) (hO : O' ⊆ O) : IsChart c Ψ O' :=
  ⟨h.1.mono hO, fun z hz => h.2 z (hO hz)⟩

/-- `bpP:p1:chart`: the pulled-back Hamiltonian `H^Ψ = c⁻¹ (H ∘ Ψ)`. -/
def chartPullback (c : ℝ) (H : Phase d → ℝ) (Ψ : Phase d → Phase d) : Phase d → ℝ :=
  fun z => c⁻¹ * H (Ψ z)

/-- Remark after `bpP:p1:chart`: `DΨ(z)` is invertible on `O`. -/
theorem IsChart.bijective_fderiv {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) {z : Phase d} (hz : z ∈ O) : Bijective (fderiv ℝ Ψ z) :=
  bijective_of_symplectic hc.ne' (h.2 z hz)

/-- `stepP:p1:li-det`: `|det DΨ| = c^d` on `O`. -/
theorem IsChart.abs_det_fderiv {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) {z : Phase d} (hz : z ∈ O) :
    |LinearMap.det (fderiv ℝ Ψ z : Phase d →ₗ[ℝ] Phase d)| = c ^ d := by
  rw [abs_det_of_symplectic hc.ne' (h.2 z hz), abs_of_pos hc]

private theorem linearField_smul (r : ℝ) (ℓ : Phase d →L[ℝ] ℝ) :
    linearField (r • ℓ) = r • linearField ℓ := by
  simp [linearField, Prod.ext_iff, funext_iff]

private theorem linearField_zero : linearField (0 : Phase d →L[ℝ] ℝ) = 0 := by
  simp [linearField]; rfl

/-- `bpP:p1:chart-field`, `stepP:p1:cf-diff`. -/
theorem chart_field_differentiableAt_iff {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d}
    {O : Set (Phase d)} (h : IsChart c Ψ O) (H : Phase d → ℝ) {z : Phase d} (hz : z ∈ O) :
    DifferentiableAt ℝ (chartPullback c H Ψ) z ↔ DifferentiableAt ℝ H (Ψ z) := by
  have hΨ : DifferentiableAt ℝ Ψ z := (h.1 z hz).differentiableAt
  constructor
  · intro hG
    have hs : HasStrictFDerivAt Ψ (fderiv ℝ Ψ z) z := (h.1 z hz).hasStrictFDerivAt
    let e : Phase d ≃L[ℝ] Phase d :=
      (LinearEquiv.ofBijective (fderiv ℝ Ψ z : Phase d →ₗ[ℝ] Phase d)
        (h.bijective_fderiv hc hz)).toContinuousLinearEquiv
    have he : (e : Phase d →L[ℝ] Phase d) = fderiv ℝ Ψ z := by
      ext w <;> rfl
    have hs' : HasStrictFDerivAt Ψ (e : Phase d →L[ℝ] Phase d) z := by rw [he]; exact hs
    have hloc := hs'.to_localInverse
    have hz' : hs'.localInverse Ψ e z (Ψ z) = z := hs'.localInverse_apply_image
    have hGg : DifferentiableAt ℝ (chartPullback c H Ψ) (hs'.localInverse Ψ e z (Ψ z)) := by
      rw [hz']; exact hG
    have hcomp : DifferentiableAt ℝ
        (fun w => c * chartPullback c H Ψ (hs'.localInverse Ψ e z w)) (Ψ z) :=
      (hGg.comp (Ψ z) hloc.hasFDerivAt.differentiableAt).const_mul c
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hs'.eventually_right_inverse] with w hw
    simp only [chartPullback, hw]
    field_simp
  · intro hH
    exact (hH.comp z hΨ).const_mul _ |>.congr_of_eventuallyEq (Filter.EventuallyEq.refl _ _)

/-- `bpP:p1:chart-field`, `stepP:p1:cf-field`: `DΨ(z) X_{H^Ψ}(z) = X_H(Ψ z)` (unconditionally). -/
theorem chart_field {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) (H : Phase d → ℝ) {z : Phase d} (hz : z ∈ O) :
    fderiv ℝ Ψ z (hamiltonianVectorField (chartPullback c H Ψ) z) =
      hamiltonianVectorField H (Ψ z) := by
  have hΨ : DifferentiableAt ℝ Ψ z := (h.1 z hz).differentiableAt
  by_cases hH : DifferentiableAt ℝ H (Ψ z)
  · have hd : fderiv ℝ (chartPullback c H Ψ) z =
        c⁻¹ • (fderiv ℝ H (Ψ z)).comp (fderiv ℝ Ψ z) := by
      have := (hH.hasFDerivAt.comp z hΨ.hasFDerivAt).const_mul c⁻¹
      exact this.fderiv
    rw [hamiltonianVectorField_eq_linearField, hamiltonianVectorField_eq_linearField, hd,
      linearField_smul, map_smul,
      apply_linearField_comp_of_symplectic hc.ne' (h.2 z hz), smul_smul,
      inv_mul_cancel₀ hc.ne', one_smul]
  · have hG : ¬ DifferentiableAt ℝ (chartPullback c H Ψ) z :=
      fun hG => hH ((chart_field_differentiableAt_iff hc h H hz).1 hG)
    rw [hamiltonianVectorField_eq_linearField, hamiltonianVectorField_eq_linearField,
      fderiv_zero_of_not_differentiableAt hG, fderiv_zero_of_not_differentiableAt hH,
      linearField_zero, map_zero]

/-- `bpP:p1:chart-orbit` (pointwise in `t`; `J` any set). -/
theorem chart_orbit {c : ℝ} (hc : 0 < c) {Ψ : Phase d → Phase d} {O : Set (Phase d)}
    (h : IsChart c Ψ O) {H : Phase d → ℝ} {J : Set ℝ} {y : ℝ → Phase d}
    (hyO : ∀ t ∈ J, y t ∈ O)
    (hy : ∀ t ∈ J, DifferentiableAt ℝ (chartPullback c H Ψ) (y t) ∧
      HasDerivAt y (hamiltonianVectorField (chartPullback c H Ψ) (y t)) t) :
    ∀ t ∈ J, DifferentiableAt ℝ H (Ψ (y t)) ∧
      HasDerivAt (Ψ ∘ y) (hamiltonianVectorField H (Ψ (y t))) t := by
  intro t ht
  refine ⟨(chart_field_differentiableAt_iff hc h H (hyO t ht)).1 (hy t ht).1, ?_⟩
  have hΨ : DifferentiableAt ℝ Ψ (y t) := (h.1 _ (hyO t ht)).differentiableAt
  have := hΨ.hasFDerivAt.comp_hasDerivAt t (hy t ht).2
  rwa [chart_field hc h H (hyO t ht)] at this

/-- `bpP:p1:typical` (3): composition of charts. -/
theorem IsChart.comp {c₁ c₂ : ℝ} {Ψ₁ Ψ₂ : Phase d → Phase d} {O₁ O₂ : Set (Phase d)}
    (h₁ : IsChart c₁ Ψ₁ O₁) (h₂ : IsChart c₂ Ψ₂ O₂) (hmaps : MapsTo Ψ₁ O₁ O₂) :
    IsChart (c₁ * c₂) (Ψ₂ ∘ Ψ₁) O₁ := by
  refine ⟨h₂.1.comp h₁.1 hmaps, ?_⟩
  have := IsSymplecticOn.comp h₁.2 h₂.2 (fun z hz => (h₁.1 z hz).differentiableAt)
    (fun z hz => (h₂.1 z hz).differentiableAt) hmaps
  rwa [mul_comm c₂ c₁] at this

/-- `bpP:p1:typical` (3): `(H^{Ψ₂})^{Ψ₁} = H^{Ψ₂ ∘ Ψ₁}`. -/
theorem chartPullback_comp (c₁ c₂ : ℝ) (H : Phase d → ℝ) (Ψ₁ Ψ₂ : Phase d → Phase d) :
    chartPullback c₁ (chartPullback c₂ H Ψ₂) Ψ₁ = chartPullback (c₁ * c₂) H (Ψ₂ ∘ Ψ₁) := by
  funext z
  simp only [chartPullback, Function.comp_apply, mul_inv, mul_assoc]

/-- A continuous linear equivalence that is conformally symplectic is a chart on every set
(used for `phaseCast`, `angleScale`). -/
theorem isChart_continuousLinearEquiv {c : ℝ} (L : Phase d ≃L[ℝ] Phase d)
    (hL : ∀ u v, symplecticForm (L u) (L v) = c * symplecticForm u v) (O : Set (Phase d)) :
    IsChart c L O := by
  refine ⟨fun z _ => (L : Phase d →L[ℝ] Phase d).analyticAt z, ?_⟩
  intro z _ u v
  rw [ContinuousLinearEquiv.fderiv]
  exact hL u v

/-- `bpP:p1:conv#data`: `S_c(z₁, z₂) = (c z₁, z₂)` (Kepler design: `angleScale`, P7-6). -/
def angleScale (c : ℝ) (z : Phase d) : Phase d := (c • z.1, z.2)

/-- `S_c` as a continuous linear map. -/
def angleScaleCLM (c : ℝ) : Phase d →L[ℝ] Phase d :=
  ((c • ContinuousLinearMap.id ℝ (Fin d → ℝ)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.snd ℝ _ _)

theorem angleScaleCLM_apply (c : ℝ) (z : Phase d) : angleScaleCLM c z = angleScale c z := rfl

/-- The full `2π`-lattice `(2π k, 0)` (Kepler design: `fullShift`, P7-6; here for every `d`). -/
def fullShift (k : Fin d → ℤ) : Phase d := (fun i => 2 * π * (k i : ℝ), 0)

theorem fullShift_eq_angleScale (k : Fin d → ℤ) : fullShift k = angleScale (2 * π) (angleShift k) :=
  by
  refine Prod.ext (funext fun i => ?_) rfl
  simp [fullShift, angleScale, angleShift]

private theorem angleScale_eq_clm (c : ℝ) : (angleScale c : Phase d → Phase d) = angleScaleCLM c :=
  rfl

private theorem angleScale_symplectic (c : ℝ) (u v : Phase d) :
    symplecticForm (angleScale c u) (angleScale c v) = c * symplecticForm u v := by
  simp only [symplecticForm, angleScale, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `bpP:p1:period-convert` (a): `S_c` is a `c`-chart on all of phase space. -/
theorem isChart_angleScale {c : ℝ} (hc : 0 < c) : IsChart c (angleScale c) (univ : Set (Phase d)) :=
  by
  refine ⟨fun z _ => (angleScaleCLM c).analyticAt z, ?_⟩
  intro z _ u v
  rw [angleScale_eq_clm, ContinuousLinearMap.fderiv]
  exact angleScale_symplectic c u v

/-- (a) the lattice formula `S_c(z + ι_k) = S_c z + (c k, 0)`. -/
theorem angleScale_add_angleShift (c : ℝ) (z : Phase d) (k : Fin d → ℤ) :
    angleScale c (z + angleShift k) = angleScale c z + (fun i => c * (k i : ℝ), 0) := by
  refine Prod.ext (funext fun i => ?_) (by simp [angleScale, angleShift])
  simp [angleScale, angleShift]

/-- (a) `|det DS_c| = c^d`. -/
theorem abs_det_fderiv_angleScale {c : ℝ} (hc : 0 < c) (z : Phase d) :
    |LinearMap.det (fderiv ℝ (angleScale c) z : Phase d →ₗ[ℝ] Phase d)| = c ^ d :=
  (isChart_angleScale hc).abs_det_fderiv hc (mem_univ z)

/-- (a) consequence used by `bpP:p1:measure-use`: `S_c` multiplies Lebesgue measure by `c^d`. -/
theorem volume_angleScale_image {c : ℝ} (hc : 0 < c) (A : Set (Phase d)) :
    volume (angleScale c '' A) = ENNReal.ofReal (c ^ d) * volume A := by
  have : (volume : Measure (Phase d)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have h := Measure.addHaar_image_continuousLinearMap (volume : Measure (Phase d))
    (angleScaleCLM c) A
  have hdet : |LinearMap.det ((angleScaleCLM c : Phase d →L[ℝ] Phase d) : Phase d →ₗ[ℝ] Phase d)| =
      c ^ d := by
    have := abs_det_fderiv_angleScale hc (0 : Phase d)
    rwa [angleScale_eq_clm, ContinuousLinearMap.fderiv] at this
  rw [hdet] at h
  exact h

/-- (b) the Hamiltonian dictionary: `H̃^{S_c}(z₁, z₂) = c⁻¹ H̃(c z₁, z₂)`. -/
theorem chartPullback_angleScale (c : ℝ) (H : Phase d → ℝ) (z : Phase d) :
    chartPullback c H (angleScale c) z = c⁻¹ * H (c • z.1, z.2) := rfl

/-- (b) `S_c X_{H̃^{S_c}}(z) = X_{H̃}(S_c z)` for every `z`. -/
theorem angleScale_hamiltonianVectorField {c : ℝ} (hc : 0 < c) (H : Phase d → ℝ) (z : Phase d) :
    angleScale c (hamiltonianVectorField (chartPullback c H (angleScale c)) z) =
      hamiltonianVectorField H (angleScale c z) := by
  have := chart_field hc (isChart_angleScale hc) H (mem_univ z)
  rwa [angleScale_eq_clm, ContinuousLinearMap.fderiv] at this

/-- (d) the frozen fast shift is `S_{2π}` applied to `((k_f, 0_b), 0)`. -/
theorem fastShift_eq_angleScale {a b : ℕ} (k : Fin a → ℤ) :
    fastShift (b := b) k =
      angleScale (2 * π) (Fin.append (fun i => (k i : ℝ)) (0 : Fin b → ℝ), 0) := by
  refine Prod.ext (funext fun i => ?_) rfl
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [fastShift, angleScale, Fin.append_left]
  · simp [fastShift, angleScale, Fin.append_right]

end Chart

end KAM.Planetary

end
