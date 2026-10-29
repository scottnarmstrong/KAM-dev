/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.FlowRegular
public import KAM.Canonical.SymplecticForm

/-!
# The Hamiltonian flow is symplectic; canonical maps

Blueprint-N Part 5, nodes `bpN:p5:symplectic` and `bpN:p5:canonical`.

* `KAM.Canonical.symplectic`: for `Y = DX^t_φ(z)`: `ω(Yv, Yw) = ω(v, w)`, `ξ(Y J(η∘Y)) = ξ(Jη)`
  and `det Y = ±1`.
* `KAM.Canonical.canonical_bracket`, `canonical_field`, `canonical_orbit`: the flow map
  preserves brackets, intertwines Hamiltonian fields, and transfers orbits.

Proof of `symplectic`. `Y(τ) = DX^τ(z)` solves `Y' = DF(X^τ z) Y` (the variational equation of
`flow_b`, differentiated by the fundamental theorem of calculus), and `DF = DX_φ` is
`ω`-skew (`symplFormC_fderiv_field_skew`, from the symmetry of `D²φ`), so `ω(Yv, Yw)` has zero
derivative; `Y(0) = 1`. The rest is linear algebra (`SymplecticForm`).
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace KAM.Canonical

/-! ### The derivative of the flow in time -/

section TimeDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A continuous function on `[-1, 1]` with zero derivative on `(-1, 1)` is constant. -/
theorem eq_of_hasDerivAt_Ioo {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : ℝ → G}
    (hc : ContinuousOn g (Icc (-1) 1)) (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt g 0 x) :
    ∀ t ∈ Icc (-1 : ℝ) 1, g t = g 0 := by
  intro t ht
  rcases le_total 0 t with h0 | h0
  · refine constant_of_has_deriv_right_zero (f := g) (a := 0) (b := t)
      (hc.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩) (fun x hx => ?_) t
      ⟨h0, le_rfl⟩
    exact (hd x ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩).hasDerivWithinAt
  · have key := constant_of_has_deriv_right_zero (f := fun s => g (-s)) (a := 0) (b := -t)
      (hc.comp continuous_neg.continuousOn fun x hx => ⟨by linarith [hx.2, ht.1],
        by linarith [hx.1]⟩) (fun x hx => ?_) (-t) ⟨by linarith, le_rfl⟩
    · simpa using key
    · have h1 : HasDerivAt g 0 (-x) :=
        hd (-x) ⟨by linarith [hx.2, ht.1], by linarith [hx.1]⟩
      have := h1.scomp x (hasDerivAt_neg x)
      exact (this.congr_deriv (by simp)).hasDerivWithinAt

/-- `t ↦ DX^t(z)` is continuous on `[-1, 1]`. -/
theorem continuousOn_flow_fderiv_time {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) :
    ContinuousOn (fun σ : ℝ => fderiv ℂ (flow F Ω σ) z) (Icc (-1) 1) :=
  (flow_b h).2.2.2.1.comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hσ => ⟨hσ, hz⟩

/-- `DX⁰(z) = 1`. -/
theorem fderiv_flow_zero {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) :
    fderiv ℂ (flow F Ω 0) z = ContinuousLinearMap.id ℂ E := by
  have := (flow_b h).2.2.2.2 0 ⟨by norm_num, by norm_num⟩ z hz
  simpa using this

/-- The variational equation in differential form: `d/dτ DX^τ(z) = DF(X^τ z) DX^τ(z)` on
`(-1, 1)`. -/
theorem hasDerivAt_flow_fderiv {W : E ≃L[ℂ] E} {Ω : Set E} {F : E → E} {ε : ℝ}
    (h : SmallField W Ω F ε) {z : E} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {τ : ℝ}
    (hτ : τ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun σ : ℝ => fderiv ℂ (flow F Ω σ) z)
      ((fderiv ℂ F (flow F Ω τ z)).comp (fderiv ℂ (flow F Ω τ) z)) τ := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hU := isOpen_gaugeInterior h.isOpen W (1 / 2)
  have hp := flow_paramHyp h
  have hmap := (flow_b h).2.2.1
  obtain ⟨hg, hder⟩ := ParamHyp.comp_field h hU hp hmap
  set f : ℝ → (E →L[ℂ] E) := fun σ =>
    (fderiv ℂ F (flow F Ω σ z)).comp (fderiv ℂ (flow F Ω σ) z) with hf
  have hfc : ContinuousOn f (Icc (-1) 1) := by
    have := hg.contD.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun σ hσ => (⟨hσ, hz⟩ : (σ, z).1 ∈ Icc (-1 : ℝ) 1 ∧ (σ, z).2 ∈ _))
    exact this.congr fun σ hσ => (hder σ hσ z hz).symm
  have hIcc : Icc (-1 : ℝ) 1 ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hint : IntervalIntegrable f volume 0 τ :=
    (hfc.mono (uIcc_subset_Icc h0 (Ioo_subset_Icc_self hτ))).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter f (𝓝 τ) :=
    (hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ
  have hd : HasDerivAt (fun σ : ℝ => ContinuousLinearMap.id ℂ E + ∫ s in (0 : ℝ)..σ, f s) (f τ) τ :=
    ((intervalIntegral.integral_hasDerivAt_right hint hmeas (hfc.continuousAt hIcc))).const_add _
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hIcc] with σ hσ
  exact (flow_b h).2.2.2.2 σ hσ z hz

end TimeDerivative

/-! ### Symplecticity of the Hamiltonian flow -/

section Hamiltonian

variable {n : ℕ}

theorem continuousOn_symplFormC_apply {s : Set ℝ}
    {Y : ℝ → ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    (hY : ContinuousOn Y s) (v w : (Fin n → ℂ) × (Fin n → ℂ)) :
    ContinuousOn (fun σ => symplFormC (Y σ v) (Y σ w)) s := by
  have h1 : ContinuousOn (fun σ => Y σ v) s := hY.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun σ => Y σ w) s := hY.clm_apply continuousOn_const
  unfold symplFormC
  refine continuousOn_finsetSum _ fun i _ => ?_
  have h1a := (continuous_apply i).comp_continuousOn ((continuous_fst).comp_continuousOn h1)
  have h1b := (continuous_apply i).comp_continuousOn ((continuous_snd).comp_continuousOn h1)
  have h2a := (continuous_apply i).comp_continuousOn ((continuous_fst).comp_continuousOn h2)
  have h2b := (continuous_apply i).comp_continuousOn ((continuous_snd).comp_continuousOn h2)
  exact (h1b.mul h2a).sub (h1a.mul h2b)

/-- Form invariance: `ω(DX^t(z) v, DX^t(z) w) = ω(v, w)`. -/
theorem flow_symplFormC {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (v w : (Fin n → ℂ) × (Fin n → ℂ)) :
    symplFormC (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z v)
        (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z w) = symplFormC v w := by
  set F := KAM.hamiltonianVectorFieldℂ φ with hF
  set Y : ℝ → _ := fun σ => fderiv ℂ (flow F Ω σ) z with hY
  have hYc : ContinuousOn Y (Icc (-1) 1) := continuousOn_flow_fderiv_time h hz
  have hgc : ContinuousOn (fun σ => symplFormC (Y σ v) (Y σ w)) (Icc (-1) 1) :=
    continuousOn_symplFormC_apply hYc v w
  have hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun σ => symplFormC (Y σ v) (Y σ w)) 0 x := by
    intro x hx
    have hY' := hasDerivAt_flow_fderiv h hz hx
    have hxΩ : flow F Ω x z ∈ Ω := (flow_b h).2.2.1 x (Ioo_subset_Icc_self hx) z hz
    have hv := (((ContinuousLinearMap.apply ℂ _ v).restrictScalars ℝ).hasFDerivAt
        (x := fderiv ℂ (flow F Ω x) z)).comp_hasDerivAt x hY'
    have hw := (((ContinuousLinearMap.apply ℂ _ w).restrictScalars ℝ).hasFDerivAt
        (x := fderiv ℂ (flow F Ω x) z)).comp_hasDerivAt x hY'
    have hskew := symplFormC_fderiv_field_skew h.isOpen hφ hxΩ (Y x v) (Y x w)
    refine (hasDerivAt_symplFormC hv hw).congr_deriv ?_
    simpa using hskew
  have := eq_of_hasDerivAt_Ioo hgc hgd t ht
  simp only [hY] at this
  rw [this, fderiv_flow_zero h hz]
  rfl

/-- `bpN:p5:symplectic`: `YᵀJY = J` (form invariance), `YJYᵀ = J` (the bracket of linear
functionals is preserved), `det Y = ±1`, for `Y = DX^t(z)`. -/
theorem symplectic {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (Y : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)))
    (hY : Y = fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z) :
    (∀ v w, symplFormC (Y v) (Y w) = symplFormC v w) ∧
    (∀ ξ η : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ,
      (ξ.comp Y) (KAM.hamiltonianJ (η.comp Y)) = ξ (KAM.hamiltonianJ η)) ∧
    (Y.det = 1 ∨ Y.det = -1) := by
  have hform : ∀ v w, symplFormC (Y v) (Y w) = symplFormC v w := by
    subst hY
    exact flow_symplFormC hφ h hz ht
  refine ⟨hform, fun ξ η => ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, map_hamiltonianJ_comp Y hform]
  · exact det_eq_one_or_neg_one (Y : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] _) hform

/-! ### Canonical maps -/

/-- The data shared by the three `canonical` statements. -/
private theorem flow_fderiv_J {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    (hzU : flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ U)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hH : DifferentiableOn ℂ H U) :
    DifferentiableAt ℂ (fun w => H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z ∧
    fderiv ℂ (fun w => H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z =
      (fderiv ℂ H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)).comp
        (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z) ∧
    fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z
        (KAM.hamiltonianVectorFieldℂ (fun w => H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z) =
      KAM.hamiltonianVectorFieldℂ H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) := by
  have hdΦ : DifferentiableAt ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z :=
    ((flow_b h).2.1 t ht).differentiableAt
      ((isOpen_gaugeInterior h.isOpen W (1 / 2)).mem_nhds hz)
  have hH' : DifferentiableAt ℂ H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) :=
    hH.differentiableAt (hU.mem_nhds hzU)
  have hc := hH'.hasFDerivAt.comp z hdΦ.hasFDerivAt
  have hform := flow_symplFormC hφ h hz ht
  have hf : fderiv ℂ (fun w => H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z =
      (fderiv ℂ H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)).comp
        (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z) := hc.fderiv
  refine ⟨hc.differentiableAt, hf, ?_⟩
  rw [KAM.hamiltonianVectorFieldℂ_eq_J _ z, hf, KAM.hamiltonianVectorFieldℂ_eq_J H]
  exact map_hamiltonianJ_comp _ hform _

/-- `bpN:p5:canonical` (a): bracket invariance (and `u ∘ Φ` is holomorphic near `z`). -/
theorem canonical_bracket {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    (hzU : flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ U)
    {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : DifferentiableOn ℂ u U)
    (hv : DifferentiableOn ℂ v U) :
    DifferentiableAt ℂ (fun w => u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z ∧
    poissonBracket (fun w => u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w))
        (fun w => v (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z =
      poissonBracket u v (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) := by
  obtain ⟨hdu, hfu, -⟩ := flow_fderiv_J hφ h hz ht hU hzU hu
  obtain ⟨-, hfv, hJv⟩ := flow_fderiv_J hφ h hz ht hU hzU hv
  refine ⟨hdu, ?_⟩
  rw [poissonBracket_eq_fderiv_field, poissonBracket_eq_fderiv_field, hfu,
    ContinuousLinearMap.comp_apply, hJv]

/-- `bpN:p5:canonical` (b): `DΦ(z) X_{H∘Φ}(z) = X_H(Φ z)`. -/
theorem canonical_field {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    (hzU : flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ U)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hH : DifferentiableOn ℂ H U) :
    fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) z
        (KAM.hamiltonianVectorFieldℂ (fun w => H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) z) =
      KAM.hamiltonianVectorFieldℂ H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) :=
  (flow_fderiv_J hφ h hz ht hU hzU hH).2.2

/-- `bpN:p5:canonical` (c): orbits transfer. -/
theorem canonical_orbit {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hH : DifferentiableOn ℂ H U) {J : Set ℝ}
    {y : ℝ → (Fin n → ℂ) × (Fin n → ℂ)}
    (hy : ∀ τ ∈ J, y τ ∈ gaugeInterior W Ω (1 / 2) ∧
      HasDerivAt y (KAM.hamiltonianVectorFieldℂ
        (fun w => H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t w)) (y τ)) τ)
    (hyU : ∀ τ ∈ J, flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (y τ) ∈ U) :
    ∀ τ ∈ J, HasDerivAt (fun s => flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (y s))
      (KAM.hamiltonianVectorFieldℂ H (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t (y τ))) τ := by
  intro τ hτ
  obtain ⟨hyz, hyd⟩ := hy τ hτ
  have hdΦ : DifferentiableAt ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t) (y τ) :=
    ((flow_b h).2.1 t ht).differentiableAt
      ((isOpen_gaugeInterior h.isOpen W (1 / 2)).mem_nhds hyz)
  have := (hdΦ.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hyd
  have e := canonical_field hφ h hyz ht hU (hyU τ hτ) hH
  exact this.congr_deriv (by simpa using e)

end Hamiltonian

end KAM.Canonical

end
