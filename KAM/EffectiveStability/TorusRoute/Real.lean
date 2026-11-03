/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusRoute.Chart

/-!
# The complexified chart restricts to the real chart (track B, package B5-ROUTE, item 3)

For `K` holomorphic on a strip and real on reals, with real data `u = torusRealU K`,
`v = torusRealV K`: `torusChartX u = torusRealX K`, the complex Jacobian at a real point is the
real Jacobian, and `Ψ_ℂ ∘ ι₂ = ι₂ ∘ Ψ` (`torusCxChart_realInclusion`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open KAM Matrix

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

theorem torusChartX_torusRealU (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) :
    torusChartX (torusRealU K) = torusRealX K := by
  funext φ
  simp [torusChartX, torusRealU]

theorem torusCxJac_realInclusion (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K) (φ : Fin n → ℝ) :
    torusCxJac K (realInclusion n φ) =
      (torusChartJac (torusRealU K) φ).map (Complex.ofReal) := by
  ext i j
  have hKd : DifferentiableAt ℂ K (realInclusion n φ) :=
    hK.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds (realInclusion_mem_complexStrip hρ φ))
  have h1 := fderiv_torusRealX_incl hρ hK hreal φ (Pi.single j 1)
  rw [realInclusion_single] at h1
  have h2 : fderiv ℂ (fun θ => (K θ).1) (realInclusion n φ) (Pi.single j 1) =
      (fderiv ℂ K (realInclusion n φ) (Pi.single j 1)).1 := by
    rw [hKd.hasFDerivAt.fst.fderiv]; rfl
  simp only [torusCxJac, Matrix.of_apply, Matrix.map_apply, torusChartJac,
    torusChartX_torusRealU, h2, ← h1]
  rfl

/-- Inverse transposes commute with the inclusion `ℝ ⊂ ℂ`. -/
theorem map_transpose_inv_mulVec {N : Matrix (Fin n) (Fin n) ℝ} (hN : N.det ≠ 0)
    (J : Fin n → ℝ) :
    ((N.map Complex.ofReal)ᵀ)⁻¹ *ᵥ (realInclusion n J) = realInclusion n (Nᵀ⁻¹ *ᵥ J) := by
  have hd : ((N.map Complex.ofReal)ᵀ).det ≠ 0 := by
    rw [det_transpose]
    have := RingHom.map_det Complex.ofRealHom N
    intro h
    apply hN
    have h' : Complex.ofRealHom N.det = 0 := by
      rw [this]; exact h
    exact Complex.ofReal_eq_zero.mp h'

  have hy : Nᵀ *ᵥ (Nᵀ⁻¹ *ᵥ J) = J := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (by rwa [det_transpose])), Matrix.one_mulVec]
  have h1 : (N.map Complex.ofReal)ᵀ *ᵥ realInclusion n (Nᵀ⁻¹ *ᵥ J) = realInclusion n J := by
    ext i
    have := RingHom.map_mulVec Complex.ofRealHom Nᵀ (Nᵀ⁻¹ *ᵥ J) i
    rw [hy] at this
    have e : (N.map Complex.ofReal)ᵀ = Nᵀ.map Complex.ofRealHom := by
      rw [Matrix.transpose_map]; rfl
    rw [e]
    exact this.symm
  rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.one_mulVec]

/-- **The complexified chart restricts to the real chart.** -/
theorem torusCxChart_realInclusion (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip n ρ))
    (hreal : IsRealOnReals K)
    (hdet : ∀ φ, (torusChartJac (torusRealU K) φ).det ≠ 0)
    (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    torusCxChart K (realInclusion₂ n w) =
      realInclusion₂ n (torusChartMap (torusRealU K) (torusRealV K) w) := by
  obtain ⟨φ, J⟩ := w
  have hK0 := realInclusion₂_realRestriction hreal φ
  have hx : (K (realInclusion n φ)).1 = realInclusion n (torusRealX K φ) := by
    rw [← hK0]; rfl
  have hv : (K (realInclusion n φ)).2 = realInclusion n (torusRealV K φ) := by
    rw [← hK0]; rfl
  have hJ := torusCxJac_realInclusion hρ hK hreal φ
  unfold torusCxChart torusChartMap
  simp only [realInclusion₂_apply, hx, hv, hJ, torusChartX_torusRealU]
  refine Prod.ext rfl ?_
  simp only [torusChartInvT]
  rw [map_add, map_transpose_inv_mulVec (hdet φ) J]

end KAM.EffectiveStability

end
