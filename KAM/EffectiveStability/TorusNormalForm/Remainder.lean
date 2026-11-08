/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusNormalForm.Basic
public import KAM.EffectiveStability.TorusNormalForm.Taylor
public import KAM.ODE.Basic

/-!
# The remainder vanishes to second order on the zero section (track B, B5-NF, item 2)

With `G = hR ∘ Ψ` of class `C³` on the open cylinder `cyl c` and `R = G - (E0 + ω'·J)`:
`R (φ, 0) = 0`, `D_J R (φ, 0) = 0`, `D_φ R (φ, 0) = 0`, `D_φ D_J R (φ, 0) = 0`, and `R` is
angle-periodic where `hR ∘ Ψ` is.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}
  {hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {E0 : ℝ} {ω' : Fin n → ℝ} {c : Fin n → ℝ}

theorem torusNF_G_zero (ht : TorusNFTorus u v hR E0 ω') (φ : Fin n → ℝ) :
    (hR ∘ torusChartMap u v) (φ, 0) = E0 := by
  simp only [Function.comp_apply, torusChartMap_zero]
  exact ht.energy φ

theorem torusNF_G_differentiableAt (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (φ : Fin n → ℝ) : DifferentiableAt ℝ (hR ∘ torusChartMap u v) (φ, 0) := by
  have hRd : DifferentiableAt ℝ hR (torusChartMap u v (φ, 0)) := by
    rw [torusChartMap_zero]; exact ht.hRdiff φ
  exact hRd.comp _ (torusChartMap_differentiable h _)

/-- `D_φ (hR ∘ Ψ) (φ, 0) = 0`: the energy is constant along the zero section. -/
theorem torusNF_dG_phi (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (φ e : Fin n → ℝ) : fderiv ℝ (hR ∘ torusChartMap u v) (φ, 0) (e, 0) = 0 := by
  have h1 : HasFDerivAt (fun φ' : Fin n → ℝ => (hR ∘ torusChartMap u v) (φ', 0))
      ((fderiv ℝ (hR ∘ torusChartMap u v) (φ, 0)).comp
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) φ :=
    HasFDerivAt.comp (g := hR ∘ torusChartMap u v)
      (f := ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) φ
      (by simpa using (torusNF_G_differentiableAt h ht φ).hasFDerivAt)
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)).hasFDerivAt
  have h2 : (fun φ' : Fin n → ℝ => (hR ∘ torusChartMap u v) (φ', 0)) = fun _ => E0 :=
    funext fun φ' => torusNF_G_zero ht φ'
  rw [h2] at h1
  have := congrArg (fun L => L e) (h1.unique (hasFDerivAt_const E0 φ))
  simpa using this

theorem zero_mem_cyl_nf (hc : ∀ j, 0 < c j) (φ : Fin n → ℝ) : (φ, (0 : Fin n → ℝ)) ∈ cyl c := by
  intro j; simpa using hc j

/-- `D_φ D_J (hR ∘ Ψ) (φ, 0) = 0`, in the order `D²G x (0, J) (e, 0)`. -/
theorem torusNF_d2G (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c)) (hc : ∀ j, 0 < c j)
    (φ J e : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (hR ∘ torusChartMap u v)) (φ, 0) (0, J) (e, 0) = 0 := by
  have hx : (φ, (0 : Fin n → ℝ)) ∈ cyl c := zero_mem_cyl_nf hc φ
  have hsymm := (hG.contDiffAt ((isOpen_cyl c).mem_nhds hx)).isSymmSndFDerivAt
    (by norm_num [minSmoothness])
  rw [hsymm (0, J) (e, 0)]
  have d1 : ContDiffOn ℝ 2 (fderiv ℝ (hR ∘ torusChartMap u v)) (cyl c) :=
    hG.fderiv_of_isOpen (isOpen_cyl c) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ (hR ∘ torusChartMap u v)) ((φ, 0) + (0 : ℝ) • (e, 0)) := by
    simp only [zero_smul, add_zero]
    exact (d1.differentiableOn (by norm_num)).differentiableAt ((isOpen_cyl c).mem_nhds hx)
  have h1 := hasDerivAt_clm_path_nfT hd (0, J)
  have h2 : (fun s : ℝ => fderiv ℝ (hR ∘ torusChartMap u v) ((φ, 0) + s • (e, 0)) (0, J)) =
      fun _ => ∑ j, ω' j * J j := funext fun s => by
    have : ((φ, (0 : Fin n → ℝ)) + s • (e, (0 : Fin n → ℝ))) = (φ + s • e, 0) := by simp
    rw [this, torusNF_dG_J h ht]
  rw [h2] at h1
  simpa using h1.unique (hasDerivAt_const (0 : ℝ) _)

theorem fderiv_torusNFRem (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c))
    {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : w ∈ cyl c) :
    fderiv ℝ (torusNFRem hR u v E0 ω') w =
      fderiv ℝ (hR ∘ torusChartMap u v) w - torusNFLin ω' := by
  have hGd : DifferentiableAt ℝ (hR ∘ torusChartMap u v) w :=
    (hG.differentiableOn (by norm_num)).differentiableAt ((isOpen_cyl c).mem_nhds hw)
  rw [torusNFRem_eq]
  exact (hGd.hasFDerivAt.sub ((torusNFLin ω').hasFDerivAt.const_add E0)).fderiv

theorem fderiv_fderiv_torusNFRem (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c))
    {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : w ∈ cyl c) :
    fderiv ℝ (fderiv ℝ (torusNFRem hR u v E0 ω')) w =
      fderiv ℝ (fderiv ℝ (hR ∘ torusChartMap u v)) w := by
  have hev : fderiv ℝ (torusNFRem hR u v E0 ω') =ᶠ[nhds w]
      fun y => fderiv ℝ (hR ∘ torusChartMap u v) y - torusNFLin ω' := by
    filter_upwards [(isOpen_cyl c).mem_nhds hw] with y hy using fderiv_torusNFRem hG hy
  rw [hev.fderiv_eq, fderiv_sub_const]

theorem torusNFRem_zero (ht : TorusNFTorus u v hR E0 ω') (φ : Fin n → ℝ) :
    torusNFRem hR u v E0 ω' (φ, 0) = 0 := by
  have := torusNF_G_zero ht φ
  simp only [torusNFRem, torusChartMap_zero]
  simp only [Function.comp_apply, torusChartMap_zero] at this
  simp [this]

theorem torusNFRem_dJ (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c)) (hc : ∀ j, 0 < c j)
    (φ J : Fin n → ℝ) : fderiv ℝ (torusNFRem hR u v E0 ω') (φ, 0) (0, J) = 0 := by
  rw [fderiv_torusNFRem hG (zero_mem_cyl_nf hc φ), FunLike.coe_sub, Pi.sub_apply,
    torusNF_dG_J h ht, torusNFLin_apply]
  simp

theorem torusNFRem_dphi (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c)) (hc : ∀ j, 0 < c j)
    (φ e : Fin n → ℝ) : fderiv ℝ (torusNFRem hR u v E0 ω') (φ, 0) (e, 0) = 0 := by
  rw [fderiv_torusNFRem hG (zero_mem_cyl_nf hc φ), FunLike.coe_sub, Pi.sub_apply,
    torusNF_dG_phi h ht, torusNFLin_apply]
  simp

theorem torusNFRem_d2 (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c)) (hc : ∀ j, 0 < c j)
    (φ J e : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (torusNFRem hR u v E0 ω')) (φ, 0) (e, 0) (0, J) = 0 := by
  have hx := zero_mem_cyl_nf hc φ
  rw [fderiv_fderiv_torusNFRem hG hx]
  have hsymm := (hG.contDiffAt ((isOpen_cyl c).mem_nhds hx)).isSymmSndFDerivAt
    (by norm_num [minSmoothness])
  rw [hsymm (e, 0) (0, J)]
  exact torusNF_d2G h ht hG hc φ J e

/-- Angle-periodicity of the remainder, from equivariance of the chart and periodicity of `hR`. -/
theorem torusNFRem_shift (h : TorusChartData u v κ)
    (hper : ∀ (k : Fin n → ℤ) (w : (Fin n → ℝ) × (Fin n → ℝ)), w ∈ cyl c →
      hR (torusChartMap u v w + KAM.ODE.angleShift k) = hR (torusChartMap u v w))
    (k : Fin n → ℤ) {w : (Fin n → ℝ) × (Fin n → ℝ)} (hw : w ∈ cyl c) :
    torusNFRem hR u v E0 ω' (w + KAM.ODE.angleShift k) = torusNFRem hR u v E0 ω' w := by
  unfold torusNFRem
  rw [torusChartMap_shift h, hper k w hw]
  simp [KAM.ODE.angleShift]

end KAM.EffectiveStability

end
