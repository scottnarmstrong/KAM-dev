/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Head.Frequency
import KAM.Strip.Analytic
import KAM.Strip.Bridges
import KAM.Strip.Regularity

/-!
# Part 1 (isoenergetic linear step): the frequency map without the Kolmogorov field

The fixed-frequency version `KAM.Head.freq_map` (items (ii)-(iii) of `bp:p4:freq-map`) carries
`KAM.Head.Data`, whose `nondeg` field is the Kolmogorov condition, unavailable for an isoenergetically nondegenerate `h`.
The proofs of (ii)-(iii) never use it; they are restated here for a Hamiltonian `h` that is
holomorphic on an open set `U` and real at the real points of `U`.

* `freq_map_local`: on the real slice of `U`, the frozen frequency map is the complex gradient,
  it is differentiable, its derivative is the (real, symmetric) complex Hessian.
* `freq_map_contDiff`: `J ↦ Re h(J)` and the frequency map are `C¹` on the real slice, and the
  derivative of `J ↦ Re h(J)` is `v ↦ ∇h ⬝ᵥ v`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Linear

open KAM
open KAM.Head (gradC hessian)

variable {n : ℕ} {U : Set (Fin n → ℂ)} {h : (Fin n → ℂ) → ℂ}

/-! ### The real slice and the gradient -/

private theorem isOpen_realSlice (hU : IsOpen U) :
    IsOpen {J : Fin n → ℝ | (fun i => (J i : ℂ)) ∈ U} :=
  hU.preimage (realInclusion n).continuous

private theorem differentiableAt_h (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    DifferentiableAt ℂ h (realInclusion n I) :=
  hh.differentiableAt (hU.mem_nhds hI)

private theorem eventually_im_h (hU : IsOpen U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    ∀ᶠ J in 𝓝 I, (h (realInclusion n J)).im = 0 := by
  filter_upwards [(isOpen_realSlice hU).mem_nhds hI] with J hJ
  exact hreal J hJ

private theorem frequencyMap_eq_gradC (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    (fun i => ((frequencyMap h I i : ℝ) : ℂ)) = gradC h (fun i => (I i : ℂ)) := by
  ext i
  have h1 := KAM.Head.fderiv_realInclusion_of_real (differentiableAt_h hU hh hI)
    (eventually_im_h hU hreal hI) (Pi.single i 1)
  rw [KAM.Head.realInclusion_single] at h1
  simp only [gradC]
  exact h1.symm

/-! ### Differentiability of the frequency map -/

private theorem differentiableAt_partial (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (i : Fin n) :
    DifferentiableAt ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n I) :=
  ((differentiableOn_fderiv_of_isOpen hU hh).clm_apply (differentiableOn_const _)).differentiableAt
    (hU.mem_nhds hI)

private theorem partial_im (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (i : Fin n) :
    (fderiv ℂ h (realInclusion n I) (Pi.single i 1)).im = 0 := by
  have h1 : ((frequencyMap h I i : ℝ) : ℂ) = fderiv ℂ h (realInclusion n I) (Pi.single i 1) :=
    congrFun (frequencyMap_eq_gradC hU hh hreal hI) i
  rw [← h1]
  exact Complex.ofReal_im _

private theorem eventually_im_partial (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (i : Fin n) :
    ∀ᶠ J in 𝓝 I, ((fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n J)).im = 0 := by
  filter_upwards [(isOpen_realSlice hU).mem_nhds hI] with J hJ
  exact partial_im hU hh hreal hJ i

private theorem frequencyMap_apply_eventuallyEq (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (i : Fin n) :
    (fun J => frequencyMap h J i) =ᶠ[𝓝 I]
      fun J => ((fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n J)).re := by
  filter_upwards [(isOpen_realSlice hU).mem_nhds hI] with J hJ
  have h1 : ((frequencyMap h J i : ℝ) : ℂ) = fderiv ℂ h (realInclusion n J) (Pi.single i 1) :=
    congrFun (frequencyMap_eq_gradC hU hh hreal hJ) i
  show frequencyMap h J i = (fderiv ℂ h (realInclusion n J) (Pi.single i 1)).re
  rw [← h1]
  exact (Complex.ofReal_re _).symm

private theorem differentiableAt_frequencyMap (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    DifferentiableAt ℝ (frequencyMap h) I := by
  rw [differentiableAt_pi]
  intro i
  exact (KAM.Head.differentiableAt_re_comp
    (differentiableAt_partial hU hh hI i)).congr_of_eventuallyEq
    (frequencyMap_apply_eventuallyEq hU hh hreal hI i)

/-! ### The derivative: the Hessian -/

private theorem fderiv_frequencyMap_apply (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (v : Fin n → ℝ) (i : Fin n) :
    ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ) =
      fderiv ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n I)
        (realInclusion n v) := by
  have hpi : fderiv ℝ (frequencyMap h) I v i = fderiv ℝ (fun J => frequencyMap h J i) I v := by
    rw [fderiv_pi (fun k => (differentiableAt_pi.1
      (differentiableAt_frequencyMap hU hh hreal hI)) k)]
    rfl
  rw [hpi, (frequencyMap_apply_eventuallyEq hU hh hreal hI i).fderiv_eq,
    KAM.Head.fderiv_realInclusion_of_real (differentiableAt_partial hU hh hI i)
      (eventually_im_partial hU hh hreal hI i) v]

private theorem fderiv_frequencyMap_eq_hessian (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (v : Fin n → ℝ) :
    (fun i => ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ)) =
      hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ) := by
  ext i
  rw [fderiv_frequencyMap_apply hU hh hreal hI v i]
  exact (KAM.Head.hessian_mulVec_apply h (realInclusion n I) (realInclusion n v) i).symm

private theorem hessian_transpose (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    (hessian h (fun i => (I i : ℂ)))ᵀ = hessian h (fun i => (I i : ℂ)) := by
  ext i j
  have hsymm := fderiv_apply_comm_of_differentiableOn hU hh
    (z := realInclusion n I) hI (Pi.single j 1) (Pi.single i 1)
  simp only [Matrix.transpose_apply, hessian, Matrix.of_apply]
  exact hsymm.symm

private theorem hessian_im (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (i j : Fin n) :
    (hessian h (fun i => (I i : ℂ)) i j).im = 0 := by
  have h1 := fderiv_frequencyMap_apply hU hh hreal hI (Pi.single j 1) i
  rw [KAM.Head.realInclusion_single] at h1
  have h2 : hessian h (fun i => (I i : ℂ)) i j =
      fderiv ℂ (fun y => fderiv ℂ h y (Pi.single i 1)) (realInclusion n I) (Pi.single j 1) := rfl
  rw [h2, ← h1]
  exact Complex.ofReal_im _

/-- `KAM.Head.freq_map` (ii), (iii) for `h` holomorphic on an open `U`, real at real points:
the K statement carries `KAM.Head.Data` (Kolmogorov), unavailable here. Same proofs. -/
theorem freq_map_local {U : Set (Fin n → ℂ)} (hU : IsOpen U) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    (fun i => ((frequencyMap h I i : ℝ) : ℂ)) = gradC h (fun i => (I i : ℂ)) ∧
    DifferentiableAt ℝ (frequencyMap h) I ∧
    (∀ v : Fin n → ℝ, (fun i => ((fderiv ℝ (frequencyMap h) I v i : ℝ) : ℂ)) =
      hessian h (fun i => (I i : ℂ)) *ᵥ fun j => (v j : ℂ)) ∧
    (hessian h (fun i => (I i : ℂ)))ᵀ = hessian h (fun i => (I i : ℂ)) ∧
    ∀ i j, (hessian h (fun i => (I i : ℂ)) i j).im = 0 :=
  ⟨frequencyMap_eq_gradC hU hh hreal hI, differentiableAt_frequencyMap hU hh hreal hI,
    fderiv_frequencyMap_eq_hessian hU hh hreal hI, hessian_transpose hU hh hI,
    hessian_im hU hh hreal hI⟩

/-! ### `C¹` regularity on the real slice -/

private theorem contDiffOn_re_comp (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) :
    ContDiffOn ℝ 2 (fun J : Fin n → ℝ => (h fun i => (J i : ℂ)).re)
      {J | (fun i => (J i : ℂ)) ∈ U} := by
  have hA : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => h (realInclusion n x))
      (realInclusion n ⁻¹' U) := (holomorphic_analytic hU hh).2.2
  have hB : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => (h (realInclusion n x)).re)
      (realInclusion n ⁻¹' U) := fun x hx => (Complex.reCLM.analyticAt _).comp (hA x hx)
  exact hB.contDiffOn ((hU.preimage (realInclusion n).continuous).uniqueDiffOn)

/-- `h ∘ ι` (real part) and `∇h` are `C¹` on the real slice of `U`. -/
theorem freq_map_contDiff {U : Set (Fin n → ℂ)} (hU : IsOpen U) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0) :
    ContDiffOn ℝ 1 (fun J : Fin n → ℝ => (h fun i => (J i : ℂ)).re)
        {J | (fun i => (J i : ℂ)) ∈ U} ∧
      ContDiffOn ℝ 1 (frequencyMap h) {J | (fun i => (J i : ℂ)) ∈ U} ∧
      ∀ J, (fun i => (J i : ℂ)) ∈ U → ∀ v : Fin n → ℝ,
        fderiv ℝ (fun J : Fin n → ℝ => (h fun i => (J i : ℂ)).re) J v = frequencyMap h J ⬝ᵥ v := by
  -- the three clauses hold for every holomorphic `h`; `hreal` is only part of the interface
  have _ := hreal
  have hφ := contDiffOn_re_comp hU hh
  have hV := isOpen_realSlice hU
  refine ⟨hφ.of_le (by norm_num), ?_, ?_⟩
  · have hd : ContDiffOn ℝ 1 (fun J : Fin n → ℝ =>
        fderiv ℝ (fun J : Fin n → ℝ => (h fun i => (J i : ℂ)).re) J)
        {J | (fun i => (J i : ℂ)) ∈ U} := hφ.fderiv_of_isOpen hV (by norm_num)
    exact contDiffOn_pi.2 fun i => hd.clm_apply contDiffOn_const
  · intro J _ v
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → ℝ) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl

end KAM.Iso.Linear

end
