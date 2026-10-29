/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Iso.Linear.FreqMap
public import KAM.Head.UnperturbedFrame
public import KAM.Frozen.Iso.Defs.BorderedHessian
import KAM.Head.HamiltonianField
import KAM.Strip.Averages

/-!
# Part 1 (isoenergetic linear step): the extended torsion at the trivial torus

Blueprint node `bpI:p1:trivial`.
For `H(θ, J) = h(J)` on `D = ℂⁿ × U` and the trivial torus `K⁰(θ) = (θ, ι I)` with
`ω = ∇h(I)` (`KAM.frequencyMap`), the extended torsion is the constant real matrix
`𝖡_h(I)` (`KAM.Iso.borderedHessian`):

* `trivial_torus`: `K⁰` is holomorphic, primary, real on reals, lies in `D`, has Gram matrix `1`
  and vanishing invariance error; `𝖳_H(θ) = 𝖡_h(I)` for every `θ`, hence `⟨𝖳_H⟩ = 𝖡_h(I)`;
  determinant, total inverse and row-sum norm of the inverse correspond under the cast
  `ℝ → ℂ`.

The frame side is the Kolmogorov `KAM.Head.*_unperturbedTorus`; the frequency map and the Hessian
are
`freq_map_local` (the Kolmogorov-free restatement of `KAM.Head.freq_map`). The torsion is
computed as in `KAM.Head.torsion_unperturbedTorus_eq`, but for `h ∘ pr₂` on `ℂⁿ × U` instead of
`KAM.Head.hbold` on `𝔇`, since `KAM.Head.Data` is not available here.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost
open KAM.Head (unperturbedTorus gradC hessian)

variable {n : ℕ}

/-! ### Finite-index real/complex matrix facts -/

/-- The determinant of a real matrix viewed over `ℂ` is the real determinant (any finite index). -/
private theorem det_map_ofReal_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : (B.map Complex.ofReal).det = (B.det : ℂ) := by
  have h := RingHom.map_det Complex.ofRealHom B
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

/-- The total inverse of a real matrix viewed over `ℂ` is the cast of the real total inverse
(also when the determinant vanishes: both are `0`). -/
private theorem inv_map_ofReal_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : (B.map Complex.ofReal)⁻¹ = (B⁻¹).map Complex.ofReal := by
  have hadj : (B.map Complex.ofReal).adjugate = B.adjugate.map Complex.ofReal := by
    have h := RingHom.map_adjugate Complex.ofRealHom B
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv',
    det_map_ofReal_fintype, hadj]
  ext i j
  simp

/-- The row-sum norm of a real matrix does not change under the cast `ℝ → ℂ`. -/
private theorem norm_map_ofReal_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : ‖B.map Complex.ofReal‖ = ‖B‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  congr 1
  simp [Matrix.map_apply]

/-! ### Derivatives of `h ∘ pr₂` -/

variable {U : Set (Fin n → ℂ)} {h : (Fin n → ℂ) → ℂ}

private theorem hasFDerivAt_pr2 (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z.2 ∈ U) :
    HasFDerivAt (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2)
      ((fderiv ℂ h z.2).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))) z :=
  (hh.differentiableAt (hU.mem_nhds hz)).hasFDerivAt.comp z hasFDerivAt_snd

private theorem fderiv_pr2 (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z.2 ∈ U) :
    fderiv ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2) z =
      (fderiv ℂ h z.2).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ)) :=
  (hasFDerivAt_pr2 hU hh hz).fderiv

private theorem differentiableOn_pr2 (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => h w.2)
      ((Set.univ : Set (Fin n → ℂ)) ×ˢ U) :=
  hh.comp differentiable_snd.differentiableOn fun _ hw => hw.2

/-- `D(Dφ)(z) v w = D(y ↦ Dφ(y) w)(z) v`. -/
private theorem fderiv_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ : E → ℂ} {z : E} (hφ : DifferentiableAt ℂ (fderiv ℂ φ) z) (v w : E) :
    fderiv ℂ (fderiv ℂ φ) z v w = fderiv ℂ (fun y => fderiv ℂ φ y w) z v := by
  rw [fderiv_clm_apply hφ (differentiableAt_const _)]
  simp

/-- The action Hessian of `h ∘ pr₂` is `∇²h`. -/
private theorem fderiv_pr2_action (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z.2 ∈ U) (i j : Fin n) :
    fderiv ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        fderiv ℂ (fun w' : (Fin n → ℂ) × (Fin n → ℂ) => h w'.2) w (0, Pi.single i 1)) z
      (0, Pi.single j 1) = hessian h z.2 i j := by
  have hVo : IsOpen ((Set.univ : Set (Fin n → ℂ)) ×ˢ U) := isOpen_univ.prod hU
  have hzV : z ∈ (Set.univ : Set (Fin n → ℂ)) ×ˢ U := ⟨Set.mem_univ _, hz⟩
  have hev : (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        fderiv ℂ (fun w' : (Fin n → ℂ) × (Fin n → ℂ) => h w'.2) w (0, Pi.single i 1)) =ᶠ[𝓝 z]
      fun w => fderiv ℂ h w.2 (Pi.single i 1) :=
    Filter.eventually_of_mem (hVo.mem_nhds hzV) fun w hw => by
      beta_reduce
      rw [fderiv_pr2 hU hh hw.2]
      rfl
  have hg : DifferentiableAt ℂ (fun I' => fderiv ℂ h I' (Pi.single i 1)) z.2 :=
    ((differentiableOn_fderiv_of_isOpen hU hh).differentiableAt (hU.mem_nhds hz)).clm_apply
      (differentiableAt_const _)
  have hgs : HasFDerivAt (fun w : (Fin n → ℂ) × (Fin n → ℂ) => fderiv ℂ h w.2 (Pi.single i 1))
      ((fderiv ℂ (fun I' => fderiv ℂ h I' (Pi.single i 1)) z.2).comp
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))) z :=
    hg.hasFDerivAt.comp z hasFDerivAt_snd
  rw [hev.fderiv_eq, hgs.fderiv]
  simp [hessian]

/-- The mixed derivative `D(y ↦ D(h ∘ pr₂)(y)(e_i, 0))` vanishes. -/
private theorem fderiv_pr2_angle (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z.2 ∈ U) (i : Fin n) (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        fderiv ℂ (fun w' : (Fin n → ℂ) × (Fin n → ℂ) => h w'.2) w (Pi.single i 1, 0)) z v = 0 := by
  have hVo : IsOpen ((Set.univ : Set (Fin n → ℂ)) ×ˢ U) := isOpen_univ.prod hU
  have hzV : z ∈ (Set.univ : Set (Fin n → ℂ)) ×ˢ U := ⟨Set.mem_univ _, hz⟩
  have hev : (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        fderiv ℂ (fun w' : (Fin n → ℂ) × (Fin n → ℂ) => h w'.2) w (Pi.single i 1, 0)) =ᶠ[𝓝 z]
      fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem (hVo.mem_nhds hzV) fun w hw => by
      beta_reduce
      rw [fderiv_pr2 hU hh hw.2]
      simp
  rw [hev.fderiv_eq]
  simp

/-! ### The torsion, the last row and the invariance error of the trivial torus -/

/-- The torsion of the trivial torus is `∇²h(ι I)`, whatever `ω` and `θ` are. -/
private theorem torsion_trivial (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    torsion (fun z => h z.2) (unperturbedTorus I) ω θ = hessian h (fun i => (I i : ℂ)) := by
  have hVo : IsOpen ((Set.univ : Set (Fin n → ℂ)) ×ˢ U) := isOpen_univ.prod hU
  have hz : ((θ, fun i => (I i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)) ∈
      (Set.univ : Set (Fin n → ℂ)) ×ˢ U := ⟨Set.mem_univ _, hI⟩
  have hdiff := differentiableOn_pr2 hh
  have hX := KAM.Head.fderiv_hamiltonianVectorField hVo hdiff hz
  have hfd : DifferentiableAt ℂ (fderiv ℂ (fun z : (Fin n → ℂ) × (Fin n → ℂ) => h z.2))
      (θ, fun i => (I i : ℂ)) :=
    (differentiableOn_fderiv_of_isOpen hVo hdiff).differentiableAt (hVo.mem_nhds hz)
  have hK : unperturbedTorus I θ = (θ, fun i => (I i : ℂ)) := rfl
  have hz2 : ((θ, fun i => (I i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)).2 ∈ U := hI
  ext i j
  simp only [torsion, hK, KAM.Head.normalFrame_unperturbedTorus, hX]
  simp only [ContinuousLinearMap.comp_apply, KAM.Head.hamJ_apply, fderiv_fderiv_apply hfd,
    fderiv_pr2_angle hU hh hz2, fderiv_pr2_action hU hh hz2]
  simp [dotℂ, omegaZero, Pi.single_apply]

/-- The frozen invariance error of the trivial torus vanishes at `ω = ∇h(I)`. -/
private theorem invarianceError_trivial (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (θ : Fin n → ℂ) :
    invarianceError (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I) θ = 0 := by
  have hgrad := (freq_map_local hU hh hreal hI).1
  have hK : unperturbedTorus I θ = (θ, fun i => (I i : ℂ)) := rfl
  have hz2 : ((θ, fun i => (I i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)).2 ∈ U := hI
  simp only [invarianceError, hK, KAM.Head.fderiv_unperturbedTorus, hamiltonianVectorFieldℂ,
    fderiv_pr2 hU hh hz2]
  ext i
  · simp [congrFun hgrad i, gradC]
  · simp

/-- The extended torsion of the trivial torus is the constant real matrix `𝖡_h(I)`. -/
private theorem extendedTorsion_trivial (hU : IsOpen U) (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) (θ : Fin n → ℂ) :
    KAM.Iso.extendedTorsion (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I) θ =
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) := by
  obtain ⟨hgrad, -, hhess, -, -⟩ := freq_map_local hU hh hreal hI
  have hK : unperturbedTorus I θ = (θ, fun i => (I i : ℂ)) := rfl
  ext (a | a) (b | b)
  · show torsion (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I) θ a b =
      ((fderiv ℝ (frequencyMap h) I (Pi.single b 1) a : ℝ) : ℂ)
    rw [torsion_trivial hU hh hI]
    have h1 := congrFun (hhess (Pi.single b 1)) a
    have hv : (fun j => (((Pi.single b 1 : Fin n → ℝ) j : ℝ) : ℂ)) =
        (Pi.single b 1 : Fin n → ℂ) := KAM.Head.realInclusion_single b
    rw [hv, Matrix.mulVec_single_one] at h1
    exact h1.symm
  · rfl
  · show fderiv ℂ (fun z => h z.2) (unperturbedTorus I θ)
        (normalFrame (unperturbedTorus I) θ b) = ((frequencyMap h I b : ℝ) : ℂ)
    have hz2 : ((θ, fun i => (I i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)).2 ∈ U := hI
    rw [hK, KAM.Head.normalFrame_unperturbedTorus, fderiv_pr2 hU hh hz2]
    have := congrFun hgrad b
    simp [gradC] at this ⊢
    exact this.symm
  · simp [KAM.Iso.extendedTorsion, KAM.Iso.borderedHessian]

/-! ### The node -/

/-- `bpI:p1:trivial`: at `K⁰(θ) = (θ, I)`, `H = h ∘ pr₂`, `ω = ∇h(I)`: `𝖳_H = ⟨𝖳_H⟩ = 𝖡_h(I)`. -/
theorem trivial_torus {U : Set (Fin n → ℂ)} (hU : IsOpen U) {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ J : Fin n → ℝ, (fun i => (J i : ℂ)) ∈ U → (h fun i => (J i : ℂ)).im = 0)
    {I : Fin n → ℝ} (hI : (fun i => (I i : ℂ)) ∈ U) :
    (Differentiable ℂ (unperturbedTorus I) ∧ (∀ ρ, IsPrimaryOnStrip (unperturbedTorus I) ρ) ∧
      IsRealOnReals (unperturbedTorus I) ∧
      (∀ θ, unperturbedTorus I θ ∈ (Set.univ : Set (Fin n → ℂ)) ×ˢ U) ∧
      ∀ θ, gramMatrix (unperturbedTorus I) θ = 1) ∧
    (∀ θ, invarianceError (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I) θ = 0) ∧
    (∀ θ, KAM.Iso.extendedTorsion (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I) θ =
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ))) ∧
    KAM.Iso.extendedTorsionAverage (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I) =
      (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) ∧
    (KAM.Iso.extendedTorsionAverage (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I)).det =
      ((KAM.Iso.borderedHessian h I).det : ℂ) ∧
    (KAM.Iso.extendedTorsionAverage (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I))⁻¹ =
      ((KAM.Iso.borderedHessian h I)⁻¹).map (fun x : ℝ => (x : ℂ)) ∧
    ‖(KAM.Iso.extendedTorsionAverage (fun z => h z.2) (unperturbedTorus I) (frequencyMap h I))⁻¹‖ =
      ‖(KAM.Iso.borderedHessian h I)⁻¹‖ := by
  have hT := extendedTorsion_trivial hU hh hreal hI
  have hAvg : KAM.Iso.extendedTorsionAverage (fun z => h z.2) (unperturbedTorus I)
      (frequencyMap h I) = (KAM.Iso.borderedHessian h I).map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    simp only [KAM.Iso.extendedTorsionAverage]
    simp only [hT, Matrix.map_apply]
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, KAM.volume_unitCube]
    simp
  refine ⟨⟨KAM.Head.differentiable_unperturbedTorus I,
    KAM.Head.isPrimaryOnStrip_unperturbedTorus I, KAM.Head.isRealOnReals_unperturbedTorus I,
    fun _ => ⟨Set.mem_univ _, hI⟩, KAM.Head.gramMatrix_unperturbedTorus I⟩,
    invarianceError_trivial hU hh hreal hI, hT, hAvg, ?_, ?_, ?_⟩
  · rw [hAvg]
    exact det_map_ofReal_fintype _
  · rw [hAvg]
    exact inv_map_ofReal_fintype _
  · rw [hAvg, inv_map_ofReal_fintype]
    exact norm_map_ofReal_fintype _

end KAM.Iso.Linear

end
