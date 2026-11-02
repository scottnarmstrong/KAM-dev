/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Product.Defs
public import KAM.Planetary.Spatial.Chart.Symplectic
public import KAM.Planetary.Spatial.Chart.Image
public import KAM.Planetary.Spatial.Chart.Diffeo

/-!
# The n-body spatial product chart: analyticity, symplecticity, image, local diffeomorphism

Source: `LP:MAIN L17 (533–578)` for `n` bodies (item 2), track LP, non-frozen.
Everything is inherited blockwise from the one-body chart `spatialPoincare` of the spatial chart:

* `analyticOnNhd_spatialPoincareProd`, `spatialPoincareProd_lattice`: analyticity on the product
  domain and invariance under the fast lattice `λ_i ↦ λ_i + 2π k_i`;
* `spatialPoincareProd_symplectic`: `IsSymplecticOn 1` in the repository's symplectic-form
  convention, i.e. the pullback of the form of `Phase (n * 3)` is `Σ_i (dI_i ∧ dλ_i + dη_i ∧ dξ_i
  + du_i ∧ dv_i)`;
* `spatialPoincareProd_image`: the image is the set of states in which every body has negative
  energy and positive `e₃`-projection `(q_i ⨯₃ p_i) ⬝ᵥ e₃ > 0`;
* `spatialPoincareProd_eq_iff`: injectivity modulo the fast lattice;
* `spatialPoincareProd_localDiffeo`: local analytic diffeomorphism.

-/

@[expose] public noncomputable section

open Set Real
open scoped ContDiff

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

variable {n : ℕ}

/-! ### Analyticity and derivative -/

/-- Item 2: analyticity of the product chart on the product of the domains (44). -/
theorem analyticOnNhd_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    AnalyticOnNhd ℝ (spatialPoincareProd ν) (spatialPoincareProdDom n) := by
  intro w hw
  have h : AnalyticAt ℝ
      (fun w : Phase (n + (n + n)) => fun i => spatialPoincare (ν i) (spatialBlockCLM i w)) w :=
    analyticAt_pi_iff.2 fun i =>
      (analyticOnNhd_spatialPoincare (hν i) _ (by simpa [spatialBlockCLM_apply] using hw i)).comp
        ((spatialBlockCLM i).analyticAt w)
  have := (ofSpatialBodiesCLM.analyticAt _).comp h
  convert this using 1
  funext w
  simp [ofSpatialBodiesCLM_apply, spatialPoincareProd_eq, spatialBlockCLM_apply]

theorem hasFDerivAt_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    HasFDerivAt (spatialPoincareProd ν)
      (ofSpatialBodiesCLM.comp (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ (spatialPoincare (ν i)) (spatialBlock w i)).comp (spatialBlockCLM i))) w := by
  have hd : ∀ i, HasFDerivAt (spatialPoincare (ν i))
      (fderiv ℝ (spatialPoincare (ν i)) (spatialBlock w i)) (spatialBlockCLM i w) := fun i => by
    rw [spatialBlockCLM_apply]
    exact (analyticOnNhd_spatialPoincare (hν i) _ (hw i)).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt
      (fun w : Phase (n + (n + n)) => fun i => spatialPoincare (ν i) (spatialBlockCLM i w))
      (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ (spatialPoincare (ν i)) (spatialBlock w i)).comp (spatialBlockCLM i)) w :=
    hasFDerivAt_pi'.2 fun i => by
      rw [ContinuousLinearMap.proj_pi]
      exact (hd i).comp w (spatialBlockCLM i).hasFDerivAt
  have h2 := ofSpatialBodiesCLM.hasFDerivAt.comp w h1
  convert h2 using 1
  funext w
  simp [ofSpatialBodiesCLM_apply, spatialPoincareProd_eq, spatialBlockCLM_apply]

theorem fderiv_spatialPoincareProd_apply {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) (u : Phase (n + (n + n))) :
    fderiv ℝ (spatialPoincareProd ν) w u =
      ofSpatialBodies fun i =>
        fderiv ℝ (spatialPoincare (ν i)) (spatialBlock w i) (spatialBlock u i) := by
  rw [(hasFDerivAt_spatialPoincareProd hν hw).fderiv]
  simp [ofSpatialBodiesCLM_apply, spatialBlockCLM_apply]

/-! ### Symplecticity -/

/-- Item 2: the product chart is symplectic, the block sum of the spatial chart item 5. -/
theorem spatialPoincareProd_symplectic {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    IsSymplecticOn 1 (spatialPoincareProd ν) (spatialPoincareProdDom n) := by
  intro w hw u v
  rw [fderiv_spatialPoincareProd_apply hν hw, fderiv_spatialPoincareProd_apply hν hw,
    symplecticForm_ofSpatialBodies, one_mul, symplecticForm_spatialBlocks]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact spatialPoincare_symplectic_at (hν i) (hw i) (spatialBlock u i) (spatialBlock v i)

/-! ### Fast lattice -/

/-- Item 2: fast-shift periodicity: the lattice shift preserves the domain and the chart value. -/
theorem spatialPoincareProd_lattice {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) (k : Fin n → ℤ) :
    spatialProdShift k w ∈ spatialPoincareProdDom n ∧
      spatialPoincareProd ν (spatialProdShift k w) = spatialPoincareProd ν w := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [spatialBlock_shift]
    exact spatialShift_mem (hw i) _
  · rw [spatialPoincareProd_eq, spatialPoincareProd_eq]
    congr 1
    funext i
    rw [spatialBlock_shift]
    exact spatialPoincare_periodic (hν i) (hw i) (k i)

/-! ### Image and injectivity modulo the lattice -/

theorem spatialPoincareProd_mem_region {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialPoincareProd ν w ∈ spatialRegionProd ν := by
  intro i
  rw [spatialPoincareProd_block]
  exact spatialPoincare_mem_region (hν i) (hw i)

/-- Item 2: the image of the product domain is the product region (negative energies, positive
`e₃`-projections). -/
theorem spatialPoincareProd_image {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    spatialPoincareProd ν '' spatialPoincareProdDom n = spatialRegionProd ν := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact spatialPoincareProd_mem_region hν hw
  · intro z hz
    have hs : ∀ i, ∃ p ∈ spatialPoincareDom,
        spatialPoincare (ν i) p = (bodyVector3 z.1 i, bodyVector3 z.2 i) := fun i => by
      have := (spatialPoincare_image (hν i)).symm.subset (hz i)
      obtain ⟨p, hp, hpz⟩ := this
      exact ⟨p, hp, hpz⟩
    choose p hp hpz using hs
    refine ⟨unblockSpatial p, fun i => by rw [spatialBlock_unblockSpatial]; exact hp i, ?_⟩
    rw [spatialPoincareProd_eq]
    have : (fun i => spatialPoincare (ν i) (spatialBlock (unblockSpatial p) i)) =
        fun i => (bodyVector3 z.1 i, bodyVector3 z.2 i) := by
      funext i
      rw [spatialBlock_unblockSpatial]; exact hpz i
    rw [this, ofSpatialBodies_bodyVector3]

/-- Item 2: injectivity modulo the fast lattice. -/
theorem spatialPoincareProd_eq_iff {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w w' : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n)
    (hw' : w' ∈ spatialPoincareProdDom n) :
    spatialPoincareProd ν w = spatialPoincareProd ν w' ↔
      ∃ k : Fin n → ℤ, w' = spatialProdShift k w := by
  constructor
  · intro h
    have hb : ∀ i, ∃ k : ℤ, spatialBlock w' i = spatialShift k (spatialBlock w i) := by
      intro i
      have := congrArg (fun z => (bodyVector3 z.1 i, bodyVector3 z.2 i)) h
      simp only [spatialPoincareProd_block] at this
      obtain ⟨k, h1, h2⟩ := (spatialPoincare_eq_iff (hν i) (hw i) (hw' i)).1 this
      exact ⟨k, Prod.ext h1 h2⟩
    choose k hk using hb
    refine ⟨k, Prod.ext (funext fun j => ?_) (funext fun j => ?_)⟩
    · refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
      · have := congrFun (congrArg Prod.fst (hk i)) 0
        simpa [spatialBlock, fast, spatialShift, spatialProdShift, fastShift,
          Fin.append_left] using this
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j'
        · have := congrFun (congrArg Prod.fst (hk i)) 1
          simpa [spatialBlock, slow, spatialShift, spatialProdShift, fastShift,
            Fin.append_right] using this
        · have := congrFun (congrArg Prod.fst (hk i)) 2
          simpa [spatialBlock, slow, spatialShift, spatialProdShift, fastShift,
            Fin.append_right] using this
    · refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
      · have := congrFun (congrArg Prod.snd (hk i)) 0
        simpa [spatialBlock, fast, spatialShift, spatialProdShift, fastShift] using this
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j'
        · have := congrFun (congrArg Prod.snd (hk i)) 1
          simpa [spatialBlock, slow, spatialShift, spatialProdShift, fastShift] using this
        · have := congrFun (congrArg Prod.snd (hk i)) 2
          simpa [spatialBlock, slow, spatialShift, spatialProdShift, fastShift] using this
  · rintro ⟨k, rfl⟩
    exact (spatialPoincareProd_lattice hν hw k).2.symm

/-! ### Local diffeomorphism -/

theorem spatialPoincareProd_fderiv_equiv {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    ∃ A : Phase (n + (n + n)) ≃L[ℝ] Phase (n * 3),
      (A : Phase (n + (n + n)) →L[ℝ] Phase (n * 3)) = fderiv ℝ (spatialPoincareProd ν) w := by
  have hs := spatialPoincareProd_symplectic hν w hw
  set A := fderiv ℝ (spatialPoincareProd ν) w with hA
  have hker : LinearMap.ker (A : Phase (n + (n + n)) →ₗ[ℝ] Phase (n * 3)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    refine eq_zero_of_symplecticForm fun v => ?_
    have := hs u v
    rw [one_mul] at this
    rw [← this]
    have hu' : A u = 0 := hu
    rw [hu']
    simp [symplecticForm]
  have hinj : Function.Injective (A : Phase (n + (n + n)) →ₗ[ℝ] Phase (n * 3)) :=
    LinearMap.ker_eq_bot.1 hker
  have hdim : Module.finrank ℝ (Phase (n + (n + n))) = Module.finrank ℝ (Phase (n * 3)) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  have hsurj : Function.Surjective (A : Phase (n + (n + n)) →ₗ[ℝ] Phase (n * 3)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  refine ⟨ContinuousLinearEquiv.ofBijective A hker ?_, ?_⟩
  · exact LinearMap.range_eq_top.2 hsurj
  · exact ContinuousLinearMap.ext fun z => rfl

/-- Item 2: at every point of the product domain the chart is a local analytic diffeomorphism. -/
theorem spatialPoincareProd_localDiffeo {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    ∃ φ : OpenPartialHomeomorph (Phase (n + (n + n))) (Phase (n * 3)), w ∈ φ.source ∧
      (φ : Phase (n + (n + n)) → Phase (n * 3)) = spatialPoincareProd ν ∧
        AnalyticOnNhd ℝ φ.symm φ.target := by
  have hana := analyticOnNhd_spatialPoincareProd hν
  obtain ⟨A, hA⟩ := spatialPoincareProd_fderiv_equiv hν hw
  have hc : ContDiffAt ℝ ω (spatialPoincareProd ν) w := (hana w hw).contDiffAt
  have hf' : HasFDerivAt (spatialPoincareProd ν)
      (A : Phase (n + (n + n)) →L[ℝ] Phase (n * 3)) w := by
    rw [hA]; exact (hana w hw).differentiableAt.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let φ0 := hc.toOpenPartialHomeomorph (spatialPoincareProd ν) hf' hn
  let φ := φ0.restrOpen (spatialPoincareProdDom n) (isOpen_spatialPoincareProdDom n)
  have hcoe : (φ : Phase (n + (n + n)) → Phase (n * 3)) = spatialPoincareProd ν := rfl
  refine ⟨φ, ⟨hc.mem_toOpenPartialHomeomorph_source hf' hn, hw⟩, hcoe, ?_⟩
  intro y hy
  have hxs : φ.symm y ∈ φ.source := φ.map_target hy
  have hx : φ.symm y ∈ spatialPoincareProdDom n := hxs.2
  obtain ⟨B, hB⟩ := spatialPoincareProd_fderiv_equiv hν hx
  have hB' : HasFDerivAt φ (B : Phase (n + (n + n)) →L[ℝ] Phase (n * 3)) (φ.symm y) := by
    rw [hcoe, hB]
    exact (hana _ hx).differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℝ ω φ (φ.symm y) := by
    rw [hcoe]; exact (hana _ hx).contDiffAt
  exact (φ.contDiffAt_symm hy hB' hcd).analyticAt

end KAM.Planetary.Spatial

end
