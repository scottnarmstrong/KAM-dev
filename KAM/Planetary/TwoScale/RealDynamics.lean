/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.Setting
public import KAM.Canonical.SymplecticForm
public import KAM.Strip.Regularity
public import KAM.Strip.RealRestriction

/-!
# Two-scale KAM: real dynamics bridges

`stepP:p3:inv-conj` (`real_symplectic_conjugation`): the real Hamiltonian fields of a holomorphic,
symplectic, real-on-reals map `Ψ` and a real-on-reals Hamiltonian `G` satisfy
`X_{Gr} ∘ Ψr = DΨr X_{Gr ∘ Ψr}`; the image of the open set is shown to be a neighbourhood of
each image point from the invertible derivative.

`stepP:p3:inv-lim` (`real_curve_limit`): locally uniform convergence of real differentiable curves
and their derivatives gives a differentiable limit, by Mathlib's
`hasDerivAt_of_tendsto_locally_uniformly_on'` on `univ`.
-/

public section

open Filter Set
open scoped Topology ContDiff

namespace KAM.Planetary

open KAM.Canonical

/-- `bpP:p3:inv-lim`: real locally uniform derivative-limit theorem. -/
theorem real_curve_limit {n : ℕ} {x : ℕ → ℝ → Phase n} {y v : ℝ → Phase n}
    (hx : ∀ j, Differentiable ℝ (x j))
    (hc : TendstoLocallyUniformly x y Filter.atTop)
    (hd : TendstoLocallyUniformly (fun j t => deriv (x j) t) v Filter.atTop)
    (hv : Continuous v) : ∀ t, HasDerivAt y (v t) t := by
  intro t
  have hd' : TendstoLocallyUniformlyOn (fun j t => deriv (x j) t) v Filter.atTop univ :=
    hd.tendstoLocallyUniformlyOn
  exact hasDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ hd'
    (Eventually.of_forall fun j s _ => (hx j s).differentiableWithinAt)
    (fun s _ => hc.tendstoLocallyUniformlyOn.tendsto_at (mem_univ s)) (mem_univ t)

/-- A `symplFormC`-preserving continuous linear map is bijective. -/
private theorem bijective_of_sympl {n : ℕ}
    (Y : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)))
    (hY : ∀ v w, symplFormC (Y v) (Y w) = symplFormC v w) : Function.Bijective Y := by
  have hinj : Function.Injective Y := by
    intro a b hab
    refine symplFormC_eq_of_left fun w => ?_
    rw [← hY a w, ← hY b w, hab]
  have hinj' : Function.Injective
      (Y : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))) := hinj
  exact ⟨hinj, LinearMap.surjective_of_injective hinj'⟩

/-- The image of an open set under a holomorphic map with bijective derivative is a
neighbourhood of each image point. -/
private theorem image_mem_nhds_of_sympl {n : ℕ} {V : Set (CPhase n)} (hV : IsOpen V)
    {Ψ : CPhase n → CPhase n} (hΨ : DifferentiableOn ℂ Ψ V)
    (hsym : ∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v)
    {z : CPhase n} (hz : z ∈ V) : Ψ '' V ∈ 𝓝 (Ψ z) := by
  have hsm : ContDiffOn ℂ ∞ Ψ V := KAM.contDiffOn_infty_of_differentiableOn hV hΨ
  have hstrict : HasStrictFDerivAt Ψ (fderiv ℂ Ψ z) z :=
    (hsm.contDiffAt (hV.mem_nhds hz)).hasStrictFDerivAt (by simp)
  have hb := bijective_of_sympl (fderiv ℂ Ψ z) (hsym z hz)
  let e : CPhase n ≃L[ℂ] CPhase n := ContinuousLinearEquiv.ofBijective (fderiv ℂ Ψ z)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hs : HasStrictFDerivAt Ψ (e : CPhase n →L[ℂ] CPhase n) z := hstrict
  rw [← hs.map_nhds_eq_of_equiv]
  exact image_mem_map (hV.mem_nhds hz)

/-- `bpP:p3:inv-conj`: real symplectic conjugation of Hamiltonian fields, from complex
holomorphy, symplecticity and reality. -/
theorem real_symplectic_conjugation {n : ℕ} {V : Set (CPhase n)} (hV : IsOpen V)
    {Ψ : CPhase n → CPhase n} {G : CHam n}
    (hΨ : DifferentiableOn ℂ Ψ V) (hG : DifferentiableOn ℂ G (Ψ '' V))
    (hsym : ∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v)
    (hrealΨ : ∀ x : Phase n, KAM.realInclusion₂ n x ∈ V →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hrealG : RealOn (Ψ '' V) G) :
    let Ψr := fun x : Phase n => KAM.realPartCLM₂ n (Ψ (KAM.realInclusion₂ n x))
    let Gr := fun x : Phase n => (G (KAM.realInclusion₂ n x)).re
    ∀ x : Phase n, KAM.realInclusion₂ n x ∈ V →
      KAM.hamiltonianVectorField Gr (Ψr x) =
        fderiv ℝ Ψr x (KAM.hamiltonianVectorField (Gr ∘ Ψr) x) := by
  intro Ψr Gr x hxV
  set z := KAM.realInclusion₂ n x with hzdef
  -- the real point formula for `Ψ`
  have hΨι : ∀ y : Phase n, KAM.realInclusion₂ n y ∈ V →
      Ψ (KAM.realInclusion₂ n y) = KAM.realInclusion₂ n (Ψr y) := by
    intro y hy
    obtain ⟨w, hw⟩ := hrealΨ y hy
    have : Ψr y = w := by
      show KAM.realPartCLM₂ n (Ψ (KAM.realInclusion₂ n y)) = w
      rw [← hw]; exact KAM.realPartCLM₂_realInclusion₂ w
    rw [this, hw]
  have hΨd : DifferentiableAt ℂ Ψ z := hΨ.differentiableAt (hV.mem_nhds hxV)
  -- derivative of `Ψr`
  have h2 : HasFDerivAt (fun y => Ψ (KAM.realInclusion₂ n y))
      (((fderiv ℂ Ψ z).restrictScalars ℝ).comp (KAM.realInclusion₂ n)) x :=
    (hΨd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion₂ n).hasFDerivAt
  have h3 : HasFDerivAt Ψr ((KAM.realPartCLM₂ n).comp
      (((fderiv ℂ Ψ z).restrictScalars ℝ).comp (KAM.realInclusion₂ n))) x :=
    (KAM.realPartCLM₂ n).hasFDerivAt.comp x h2
  have hmemV : ∀ᶠ y in 𝓝 x, KAM.realInclusion₂ n y ∈ V :=
    (KAM.realInclusion₂ n).continuous.continuousAt.eventually_mem (hV.mem_nhds hxV)
  have hLι : ∀ u, KAM.realInclusion₂ n (fderiv ℝ Ψr x u) =
      fderiv ℂ Ψ z (KAM.realInclusion₂ n u) := by
    intro u
    have h4 : HasFDerivAt (fun y => KAM.realInclusion₂ n (Ψr y))
        ((KAM.realInclusion₂ n).comp ((KAM.realPartCLM₂ n).comp
        (((fderiv ℂ Ψ z).restrictScalars ℝ).comp (KAM.realInclusion₂ n)))) x :=
      (KAM.realInclusion₂ n).hasFDerivAt.comp x h3
    have hev : (fun y => KAM.realInclusion₂ n (Ψr y)) =ᶠ[𝓝 x]
        fun y => Ψ (KAM.realInclusion₂ n y) := by
      filter_upwards [hmemV] with y hy using (hΨι y hy).symm
    have h5 := (h4.congr_of_eventuallyEq hev.symm).unique h2
    have := congrArg (fun L => L u) h5
    simpa [h3.fderiv] using this
  -- image point facts
  have hΨzmem : Ψ z ∈ Ψ '' V := ⟨z, hxV, rfl⟩
  have hGnhds : Ψ '' V ∈ 𝓝 (Ψ z) := image_mem_nhds_of_sympl hV hΨ hsym hxV
  have hGd : DifferentiableAt ℂ G (Ψ z) := hG.differentiableAt hGnhds
  have hGreal : ∀ y : Phase n, KAM.realInclusion₂ n y ∈ Ψ '' V →
      (G (KAM.realInclusion₂ n y)).im = 0 := hrealG
  -- field of `G` at `Ψ z`
  have hψmem : KAM.realInclusion₂ n (Ψr x) ∈ Ψ '' V := by
    rw [← hΨι x hxV]; exact hΨzmem
  have hGopen : IsOpen (Ψ '' V) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨w, hw, rfl⟩
    exact image_mem_nhds_of_sympl hV hΨ hsym hw
  have hFG := KAM.hamiltonianVectorField_eq_of_real (V := Ψ '' V) (h := G) (H := Gr) (z := Ψr x)
    hGopen hG hGreal hψmem (Eventually.of_forall fun y => rfl)
  -- field of `G ∘ Ψ` at `z`
  have hGΨ : DifferentiableOn ℂ (G ∘ Ψ) V := hG.comp hΨ (mapsTo_image Ψ V)
  have hrealGΨ : ∀ y : Phase n, KAM.realInclusion₂ n y ∈ V →
      ((G ∘ Ψ) (KAM.realInclusion₂ n y)).im = 0 := by
    intro y hy
    simp only [Function.comp]
    rw [hΨι y hy]
    exact hGreal _ (by rw [← hΨι y hy]; exact ⟨_, hy, rfl⟩)
  have hFGΨ := KAM.hamiltonianVectorField_eq_of_real (V := V) (h := G ∘ Ψ) (H := Gr ∘ Ψr) (z := x)
    hV hGΨ hrealGΨ hxV (by
      filter_upwards [hmemV] with y hy
      simp only [Function.comp, Gr]
      rw [← hΨι y hy])
  have hchain : fderiv ℂ (G ∘ Ψ) z = (fderiv ℂ G (Ψ z)).comp (fderiv ℂ Ψ z) :=
    (hGd.hasFDerivAt.comp z hΨd.hasFDerivAt).fderiv
  have hfield := map_hamiltonianJ_comp (fderiv ℂ Ψ z) (hsym z hxV) (fderiv ℂ G (Ψ z))
  apply KAM.realInclusion₂_injective n
  rw [hLι, hFG, hFGΨ, ← hzdef, KAM.hamiltonianVectorFieldℂ_eq_J, KAM.hamiltonianVectorFieldℂ_eq_J,
    hchain, hfield, ← hΨι x hxV]

end KAM.Planetary
