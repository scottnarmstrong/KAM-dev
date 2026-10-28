/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Parametric

/-!
# P Part 5: the parametric integral on a general complex normed domain

`holomorphic_parametric_integral_gen` is `KAM.Weighted.holomorphic_parametric_integral`
(`bpN:p4:ext-param`) transported along a continuous linear equivalence with `Fin q → ℂ`, so that
it applies to the product domain `ℂᵃ × ℂᵇ × ℂᵇ` of the jets.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Planetary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem holomorphic_parametric_integral_gen {p : ℕ} {Q : Set (Fin p → ℝ)} (hQ : IsCompact Q)
    {U : Set E} (hU : IsOpen U) {G : (Fin p → ℝ) → E → ℂ}
    (hG : ContinuousOn (fun y : (Fin p → ℝ) × E => G y.1 y.2) (Q ×ˢ U))
    (hGd : ∀ x ∈ Q, DifferentiableOn ℂ (G x) U)
    (hDG : ContinuousOn (fun y : (Fin p → ℝ) × E => fderiv ℂ (G y.1) y.2) (Q ×ˢ U)) :
    DifferentiableOn ℂ (fun I => ∫ x in Q, G x I) U := by
  let e : (Fin (Module.finrank ℂ E) → ℂ) ≃L[ℂ] E := (Module.finBasis ℂ E).equivFunL.symm
  have hU' : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hmap : MapsTo (fun y : (Fin p → ℝ) × (Fin (Module.finrank ℂ E) → ℂ) => (y.1, e y.2))
      (Q ×ˢ (e ⁻¹' U)) (Q ×ˢ U) := fun y hy => ⟨hy.1, hy.2⟩
  have hec : Continuous fun y : (Fin p → ℝ) × (Fin (Module.finrank ℂ E) → ℂ) => (y.1, e y.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have h := KAM.Weighted.holomorphic_parametric_integral (W := ℂ) hQ hU'
    (G := fun x w => G x (e w))
    (hG.comp hec.continuousOn hmap)
    (fun x hx => (hGd x hx).comp e.differentiable.differentiableOn (fun w hw => hw))
    (by
      have hcongr : ∀ y ∈ Q ×ˢ (e ⁻¹' U), fderiv ℂ (fun w => G y.1 (e w)) y.2 =
          (fderiv ℂ (G y.1) (e y.2)).comp (e : (Fin (Module.finrank ℂ E) → ℂ) →L[ℂ] E) := by
        intro y hy
        have hd : DifferentiableAt ℂ (G y.1) (e y.2) :=
          (hGd y.1 hy.1).differentiableAt (hU.mem_nhds hy.2)
        exact (hd.hasFDerivAt.comp y.2 e.hasFDerivAt).fderiv
      refine ContinuousOn.congr ?_ hcongr
      exact ContinuousOn.clm_comp (hDG.comp hec.continuousOn hmap) continuousOn_const)
  have h2 := h.1.comp e.symm.differentiable.differentiableOn
    (fun z hz => by simpa using hz)
  refine h2.congr fun z hz => ?_
  simp
  
end KAM.Planetary

end
