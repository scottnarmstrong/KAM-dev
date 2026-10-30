/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Torsion
public import KAM.Head.TorsionRegularGeneral

/-!
# Integrability on the unit cube, from holomorphy

The averages of the transfer lemmas (`torsionAverage_step`, `extTorsionAverage_step`,
`energyAverage_step_le`) take the integrability of their integrands as hypotheses. These are typing
data: a map holomorphic on `T_r`, `r > 0`, is continuous on `ℝⁿ`, hence integrable on the compact
cube (`integrableOn_real`). This file gives them for the objects involved, with no bound and no
`Standing`: only an open domain, a holomorphic Hamiltonian, and a holomorphic torus with invertible
Gram matrix.
-/

@[expose] public noncomputable section

open Matrix MeasureTheory

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {r : ℝ}

/-- A map holomorphic on `T_r`, `r > 0`, is integrable on the unit cube of `ℝⁿ`. -/
theorem integrableOn_real {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : (Fin n → ℂ) → F} (hr : 0 < r) (hf : DifferentiableOn ℂ f (complexStrip n r)) :
    IntegrableOn (fun x : Fin n → ℝ => f fun l => (x l : ℂ))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) :=
  integrableOn_unitCube_of_continuous (hf.continuousOn.comp_continuous
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
    (ofReal_mem_complexStrip hr))

/-- The columns of `N` are holomorphic. -/
theorem differentiableOn_normalFrame {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (j : Fin n) :
    DifferentiableOn ℂ (fun θ => normalFrame K θ j) (complexStrip n r) := by
  have hN := differentiableOn_normalMat hK hG
  have e : (fun θ => normalFrame K θ j) =
      fun θ => (sumVecIso n).symm fun s => normalMat K θ s j := funext fun θ => by
    rw [← sumVec_normalFrame, ← sumVecIso_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [e]
  exact (sumVecIso n).symm.differentiable.comp_differentiableOn
    (differentiableOn_pi.2 fun s => differentiableOn_matrix_iff_entries.1 hN s j)

/-- The entries of the torsion are integrable on the unit cube. -/
theorem integrableOn_torsion {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (ω : Fin n → ℝ) (hopen : IsOpen 𝔅) (hh : DifferentiableOn ℂ h 𝔅) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (i j : Fin n) :
    IntegrableOn (fun x : Fin n → ℝ => torsion h K ω (fun l => (x l : ℂ)) i j)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) := by
  have hN := differentiableOn_normalMat hK hG
  have hT : DifferentiableOn ℂ (torsion h K ω) (complexStrip n r) :=
    FrameAux.differentiableOn_torsion hN (FrameAux.differentiableOn_normalFieldMat
      (KAM.Head.differentiableOn_linMat hopen hh hK hK𝔅) hN)
  exact integrableOn_real hr (differentiableOn_matrix_iff_entries.1 hT i j)

/-- `H ∘ K` is integrable on the unit cube. -/
theorem integrableOn_comp {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hH : DifferentiableOn ℂ H D) (hr : 0 < r) (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    IntegrableOn (fun x : Fin n → ℝ => H (K fun l => (x l : ℂ)))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) :=
  integrableOn_real hr (hH.comp hK hKD)

/-- `DH(K) v` is integrable on the unit cube, for `v` holomorphic. -/
theorem integrableOn_fderiv_apply {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K v : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hopen : IsOpen D) (hH : DifferentiableOn ℂ H D) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hv : DifferentiableOn ℂ v (complexStrip n r)) :
    IntegrableOn (fun x : Fin n → ℝ => fderiv ℂ H (K fun l => (x l : ℂ)) (v fun l => (x l : ℂ)))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) :=
  integrableOn_real hr
    (((differentiableOn_fderiv_of_isOpen hopen hH).comp hK hKD).clm_apply hv)

/-- The last row of the bordered torsion is integrable on the unit cube. -/
theorem integrableOn_lastRow {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hopen : IsOpen D) (hH : DifferentiableOn ℂ H D) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (j : Fin n) :
    IntegrableOn (fun x : Fin n → ℝ =>
      fderiv ℂ H (K fun l => (x l : ℂ)) (normalFrame K (fun l => (x l : ℂ)) j))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) :=
  integrableOn_fderiv_apply (v := fun θ => normalFrame K θ j) hopen hH hr hK hKD
    (differentiableOn_normalFrame hK hG j)

end KAM.Sharp2.Hybrid

end
