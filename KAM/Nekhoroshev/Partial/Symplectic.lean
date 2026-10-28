/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.SymplecticLinear
public import KAM.Nekhoroshev.Partial.Flow
public import KAM.Canonical.Symplectic
public import KAM.Strip.Bridges

/-!
# Weighted symplectic structure of the extended flow (Part 11, package N11-E1)

Blueprint node `bpN:p11:symplectic`.

* `KAM.Nekhoroshev.symplectic`: the flow of a weighted Hamiltonian field is `ExtCanonical`.
  Part 5 `symplectic` is stated on `ℂⁿ × ℂⁿ`; here the variational equation of the generic flow
  is used with the weighted form `extForm c`, whose skew-symmetry on `D(wfield c φ)` is
  transported from `symplFormC_fderiv_field_skew` by the regrouping of `SymplecticLinear`.
* `symplectic_bracket`, `symplectic_det`, `symplectic_form`: consequences of `ExtCanonical`.
* `symplectic_field`: `DΨ (wfield c (v ∘ Ψ)) = wfield c v ∘ Ψ`, the field identity used by `conj`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-! ### Skew-symmetry of the linearised weighted field -/

theorem wfield_eq_regroup (c : ℝ) (hc : c ≠ 0) (φ : EC n k → ℂ) (x : EC n k) :
    wfield c φ x = (regroup c hc).symm (KAM.hamiltonianVectorFieldℂ
      (fun y => φ ((regroup c hc).symm y)) (regroup c hc x)) := by
  rw [wfield_eq_wfieldOf, wfieldOf_eq c hc, KAM.hamiltonianVectorFieldℂ_eq_J]
  have h := (regroup c hc).symm.comp_right_fderiv (f := φ) (x := regroup c hc x)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [show (fun y => φ ((regroup c hc).symm y)) = φ ∘ (regroup c hc).symm from rfl, h]
  rfl

theorem extForm_fderiv_skew (c : ℝ) (hc : c ≠ 0) {Ω : Set (EC n k)} (hΩ : IsOpen Ω)
    {φ : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω)
    (hF : DifferentiableOn ℂ (wfield c φ) Ω) {x : EC n k} (hx : x ∈ Ω) (u w : EC n k) :
    extForm c (fderiv ℂ (wfield c φ) x u) w + extForm c u (fderiv ℂ (wfield c φ) x w) = 0 := by
  set L := regroup c hc with hL
  set φ' : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ) → ℂ := fun y => φ (L.symm y) with hφ'
  set X' := KAM.hamiltonianVectorFieldℂ φ' with hX'
  have hΩ' : IsOpen (L.symm ⁻¹' Ω) := hΩ.preimage L.symm.continuous
  have hxΩ' : L x ∈ L.symm ⁻¹' Ω := by simpa using hx
  have hφ'd : DifferentiableOn ℂ φ' (L.symm ⁻¹' Ω) :=
    hφ.comp L.symm.differentiableOn (fun y hy => hy)
  have hXe : ∀ y, X' y = L (wfield c φ (L.symm y)) := fun y => by
    rw [wfield_eq_regroup c hc φ (L.symm y)]; simp [hX', hφ', hL]
  have hFd : DifferentiableAt ℂ (wfield c φ) x := hF.differentiableAt (hΩ.mem_nhds hx)
  have hXd : DifferentiableAt ℂ X' (L x) := by
    have : X' = fun y => L (wfield c φ (L.symm y)) := funext hXe
    rw [this]
    have h1 : DifferentiableAt ℂ (wfield c φ) (L.symm (L x)) := by simpa using hFd
    exact L.differentiableAt.comp (L x) (h1.comp (L x) L.symm.differentiableAt)
  have hFe : wfield c φ = fun y => L.symm (X' (L y)) := funext fun y => by
    rw [hXe]; simp
  have hD : fderiv ℂ (wfield c φ) x =
      L.symm.toContinuousLinearMap.comp ((fderiv ℂ X' (L x)).comp L.toContinuousLinearMap) := by
    have h := L.symm.hasFDerivAt.comp x (hXd.hasFDerivAt.comp x L.hasFDerivAt)
    rw [hFe]
    exact h.fderiv
  have hskew := KAM.Canonical.symplFormC_fderiv_field_skew hΩ' hφ'd hxΩ' (L u) (L w)
  rw [extForm_eq_regroup c hc, extForm_eq_regroup c hc, hD]
  simpa [hL] using hskew

/-! ### Invariance of the form along the flow -/

theorem continuousOn_symplFormC_curves {s : Set ℝ}
    {a b : ℝ → (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)} (ha : ContinuousOn a s)
    (hb : ContinuousOn b s) :
    ContinuousOn (fun σ => KAM.Canonical.symplFormC (a σ) (b σ)) s := by
  unfold KAM.Canonical.symplFormC
  refine continuousOn_finsetSum _ fun i _ => ?_
  have h1a := (continuous_apply i).comp_continuousOn ((continuous_fst).comp_continuousOn ha)
  have h1b := (continuous_apply i).comp_continuousOn ((continuous_snd).comp_continuousOn ha)
  have h2a := (continuous_apply i).comp_continuousOn ((continuous_fst).comp_continuousOn hb)
  have h2b := (continuous_apply i).comp_continuousOn ((continuous_snd).comp_continuousOn hb)
  exact (h1b.mul h2a).sub (h1a.mul h2b)

/-- A path `Y` of linear maps with `Y' = D Y`, `Y 0 = 1` and `D` skew for `extForm` preserves
`extForm`. -/
theorem extForm_const (c : ℝ) (hc : c ≠ 0) {Y D : ℝ → EC n k →L[ℂ] EC n k}
    (hYc : ContinuousOn Y (Icc (-1) 1))
    (hYd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt Y (D x) x)
    (hskew : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ a b : EC n k,
      extForm c (D x a) (Y x b) + extForm c (Y x a) (D x b) = 0)
    (hY0 : Y 0 = ContinuousLinearMap.id ℂ _) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (v w : EC n k) : extForm c (Y t v) (Y t w) = extForm c v w := by
  have hac : ∀ x : EC n k, ContinuousOn (fun σ => regroup c hc (Y σ x)) (Icc (-1) 1) := fun x =>
    (regroup c hc).continuous.comp_continuousOn (hYc.clm_apply continuousOn_const)
  have hgc : ContinuousOn (fun σ => KAM.Canonical.symplFormC (regroup c hc (Y σ v))
      (regroup c hc (Y σ w))) (Icc (-1) 1) :=
    continuousOn_symplFormC_curves (hac v) (hac w)
  have hcur : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ a : EC n k,
      HasDerivAt (fun σ => regroup c hc (Y σ a)) (regroup c hc (D x a)) x := by
    intro x hx a
    have h1 := (((ContinuousLinearMap.apply ℂ _ a).restrictScalars ℝ).hasFDerivAt
      (x := Y x)).comp_hasDerivAt x (hYd x hx)
    exact (((regroup c hc).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
      x h1
  have hgd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun σ => KAM.Canonical.symplFormC
      (regroup c hc (Y σ v)) (regroup c hc (Y σ w))) 0 x := by
    intro x hx
    have hs := hskew x hx v w
    rw [extForm_eq_regroup c hc, extForm_eq_regroup c hc] at hs
    exact (KAM.Canonical.hasDerivAt_symplFormC (hcur x hx v) (hcur x hx w)).congr_deriv hs
  have := KAM.Canonical.eq_of_hasDerivAt_Ioo hgc hgd t ht
  rw [extForm_eq_regroup c hc, extForm_eq_regroup c hc]
  refine this.trans ?_
  simp [hY0]

theorem flow_extForm (c : ℝ) (hc : c ≠ 0) {W : EC n k ≃L[ℂ] EC n k} {Ω : Set (EC n k)}
    {φ : EC n k → ℂ} {ε : ℝ} (hφ : DifferentiableOn ℂ φ Ω)
    (h : KAM.Canonical.SmallField W Ω (wfield c φ) ε) {z : EC n k}
    (hz : z ∈ KAM.Canonical.gaugeInterior W Ω (1 / 2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (v w : EC n k) :
    extForm c (fderiv ℂ (KAM.Canonical.flow (wfield c φ) Ω t) z v)
      (fderiv ℂ (KAM.Canonical.flow (wfield c φ) Ω t) z w) = extForm c v w := by
  refine extForm_const c hc (Y := fun σ => fderiv ℂ (KAM.Canonical.flow (wfield c φ) Ω σ) z)
    (D := fun σ => (fderiv ℂ (wfield c φ) (KAM.Canonical.flow (wfield c φ) Ω σ z)).comp
      (fderiv ℂ (KAM.Canonical.flow (wfield c φ) Ω σ) z))
    (KAM.Canonical.continuousOn_flow_fderiv_time h hz)
    (fun x hx => KAM.Canonical.hasDerivAt_flow_fderiv h hz hx) (fun x hx a b => ?_)
    (KAM.Canonical.fderiv_flow_zero h hz) ht v w
  have hxΩ : KAM.Canonical.flow (wfield c φ) Ω x z ∈ Ω :=
    (KAM.Canonical.flow_b h).2.2.1 x (Ioo_subset_Icc_self hx) z hz
  exact extForm_fderiv_skew c hc h.isOpen hφ h.differentiableOn hxΩ _ _

theorem symplectic {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c ε : ℝ} (hc : 0 < c)
    (φ : EC n k → ℂ) (hφ : DifferentiableOn ℂ φ Ω) (W : EC n k ≃L[ℂ] EC n k)
    (hF : KAM.Canonical.SmallField W Ω (wfield c φ) ε) {t : ℝ} (ht : |t| ≤ 1) :
    ExtCanonical c (KAM.Canonical.gaugeInterior W Ω (1/2))
      (KAM.Canonical.flow (wfield c φ) Ω t) := by
  have hc0 : c ≠ 0 := hc.ne'
  have htI : t ∈ Icc (-1 : ℝ) 1 := abs_le.1 ht
  intro z hz u v
  have hU := KAM.Canonical.isOpen_gaugeInterior hΩ W (1/2)
  have hΨ : DifferentiableAt ℂ (KAM.Canonical.flow (wfield c φ) Ω t) z :=
    ((KAM.Canonical.flow_b hF).2.1 t htI).differentiableAt (hU.mem_nhds hz)
  refine (canonical_at_iff c hc0 hΨ).2 (fun η => ?_) u v
  refine KAM.Canonical.map_hamiltonianJ_comp _ (fun a b => ?_) η
  have h := flow_extForm c hc0 hφ hF hz htI ((regroup c hc0).symm a) ((regroup c hc0).symm b)
  rw [extForm_eq_regroup c hc0, extForm_eq_regroup c hc0] at h
  simpa [conjLin_apply] using h

/-! ### Consequences of `ExtCanonical` -/

/-- The field identity: `DΨ (wfield c (v ∘ Ψ)) = wfield c v ∘ Ψ`. -/
theorem symplectic_field {c : ℝ} {U : Set (EC n k)} (hU : IsOpen U) {Ψ : EC n k → EC n k}
    (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) {z : EC n k} (hz : z ∈ U)
    {v : EC n k → ℂ} (hv : DifferentiableAt ℂ v (Ψ z)) :
    fderiv ℂ Ψ z (wfield c (fun x => v (Ψ x)) z) = wfield c v (Ψ z) := by
  have hΨz : DifferentiableAt ℂ Ψ z := hΨ.differentiableAt (hU.mem_nhds hz)
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun u => ?_
  set v' : EC n k →L[ℂ] ℂ := fderiv ℂ v (Ψ z) with hv'
  have hdv : fderiv ℂ (fun x => v (Ψ x)) z = v'.comp (fderiv ℂ Ψ z) :=
    (hv.hasFDerivAt.comp z hΨz.hasFDerivAt).fderiv
  have hdv' : fderiv ℂ (fun x => v' (Ψ x)) z = v'.comp (fderiv ℂ Ψ z) :=
    (v'.hasFDerivAt.comp z hΨz.hasFDerivAt).fderiv
  have hdu : fderiv ℂ (fun x => u (Ψ x)) z = u.comp (fderiv ℂ Ψ z) :=
    (u.hasFDerivAt.comp z hΨz.hasFDerivAt).fderiv
  have h := hcanon z hz u v'
  unfold extBracket at h
  rw [hdu, wfield_eq_wfieldOf, hdv', u.fderiv, wfield_eq_wfieldOf, v'.fderiv] at h
  rw [wfield_eq_wfieldOf, hdv, wfield_eq_wfieldOf]
  exact h

theorem symplectic_bracket {c : ℝ} {U V : Set (EC n k)} (hU : IsOpen U) (hV : IsOpen V)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hm : MapsTo Ψ U V)
    (hc : ExtCanonical c U Ψ) {u v : EC n k → ℂ}
    (hu : DifferentiableOn ℂ u V) (hv : DifferentiableOn ℂ v V) :
    ∀ z ∈ U, extBracket c (u ∘ Ψ) (v ∘ Ψ) z = extBracket c u v (Ψ z) := by
  intro z hz
  have hΨz : DifferentiableAt ℂ Ψ z := hΨ.differentiableAt (hU.mem_nhds hz)
  have huz : DifferentiableAt ℂ u (Ψ z) := hu.differentiableAt (hV.mem_nhds (hm hz))
  have hvz : DifferentiableAt ℂ v (Ψ z) := hv.differentiableAt (hV.mem_nhds (hm hz))
  have hdu : fderiv ℂ (u ∘ Ψ) z = (fderiv ℂ u (Ψ z)).comp (fderiv ℂ Ψ z) :=
    (huz.hasFDerivAt.comp z hΨz.hasFDerivAt).fderiv
  have hf := symplectic_field hU hΨ hc hz hvz
  unfold extBracket
  rw [hdu]
  exact congrArg (fderiv ℂ u (Ψ z)) hf

/-- Pointwise: `ExtCanonical` makes the regrouped derivative preserve `symplFormC`. -/
theorem canonical_form_regroup {c : ℝ} (hc : c ≠ 0) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ)
    {z : EC n k} (hz : z ∈ U) :
    ∀ a b, KAM.Canonical.symplFormC (conjLin c hc (fderiv ℂ Ψ z) a)
      (conjLin c hc (fderiv ℂ Ψ z) b) = KAM.Canonical.symplFormC a b :=
  form_of_bracket _ ((canonical_at_iff c hc (hΨ.differentiableAt (hU.mem_nhds hz))).1
    (hcanon z hz))

theorem symplectic_det {c : ℝ} (hc : 0 < c) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) :
    ∀ z ∈ U, (fderiv ℂ Ψ z).det = 1 ∨ (fderiv ℂ Ψ z).det = -1 := by
  intro z hz
  have hc0 : c ≠ 0 := hc.ne'
  have h := KAM.Canonical.det_eq_one_or_neg_one
    (conjLin c hc0 (fderiv ℂ Ψ z) : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →ₗ[ℂ] _)
    (canonical_form_regroup hc0 hU hΨ hcanon hz)
  have hdet : LinearMap.det
      (conjLin c hc0 (fderiv ℂ Ψ z) : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) →ₗ[ℂ] _) =
      (fderiv ℂ Ψ z).det := by
    have := LinearMap.det_conj (fderiv ℂ Ψ z : EC n k →ₗ[ℂ] EC n k)
      (regroup c hc0).toLinearEquiv
    exact this
  rw [hdet] at h
  exact h

theorem symplectic_form {c : ℝ} (hc : 0 < c) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) :
    ∀ z ∈ U, ∀ v w : EC n k,
      extForm c (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = extForm c v w := by
  intro z hz v w
  have hc0 : c ≠ 0 := hc.ne'
  have h := canonical_form_regroup hc0 hU hΨ hcanon hz (regroup c hc0 v) (regroup c hc0 w)
  rw [extForm_eq_regroup c hc0, extForm_eq_regroup c hc0]
  simpa [conjLin_apply] using h

/-! ### Conjugation of real orbits (`conj`) -/

section Conj

open KAM.Weighted KAM.NormalForm

private theorem extCx_eq (z : ER n k) :
    extCx z = (KAM.realInclusion n z.1, KAM.realInclusion (n+(k+k)) z.2) := by
  ext i <;> simp [extCx]

/-- The real points of `EC n k` as a continuous `ℝ`-linear map. -/
private def extCxCLM (n k : ℕ) : ER n k →L[ℝ] EC n k :=
  (KAM.realInclusion n).prodMap (KAM.realInclusion (n+(k+k)))

private theorem extCxCLM_apply (z : ER n k) : extCxCLM n k z = extCx z := (extCx_eq z).symm

private theorem extCx_eq_clm : (extCx : ER n k → EC n k) = extCxCLM n k :=
  funext fun z => (extCxCLM_apply z).symm

private theorem extCx_mem_Dom_iff (b : PartialBlock n k) {R s : ℝ} (hs : 0 < s) (z : ER n k) :
    extCx z ∈ Dom n b.base R s ↔ (extCx z).2 ∈ polyNbhd b.base R := by
  simp only [Dom, mem_prod]
  exact ⟨fun h => h.2, fun h => ⟨KAM.ofReal_mem_complexStrip hs z.1, h⟩⟩

private theorem mem_realDom_iff (b : PartialBlock n k) (R : ℝ) (z : ER n k) :
    z ∈ b.realDom R ↔ (extCx z).2 ∈ polyNbhd b.base R :=
  extCx_mem_Dom_iff b one_pos z

private theorem isOpen_realDom (b : PartialBlock n k) (R : ℝ) : IsOpen (b.realDom R) := by
  have hc : Continuous (extCx : ER n k → EC n k) := by
    rw [extCx_eq_clm]; exact (extCxCLM n k).continuous
  exact (isOpen_Dom (n := n) b.base R 1).preimage hc

private theorem hreal_of_ext {b : PartialBlock n k} {R s : ℝ} {H : EC n k → ℂ}
    (hH : ext_class b R s H) (y : ER n k) (hy : extCx y ∈ Dom n b.base R s) :
    (H (extCx y)).im = 0 := by
  have := hH.2 y (by rw [← extCx_eq]; exact hy)
  rwa [← extCx_eq] at this

private theorem realHamiltonianExt_eventually (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ)
    {z : ER n k} (hz : z ∈ b.realDom R) :
    ∀ᶠ y in nhds z, realHamiltonianExt b R H y = (H (extCx y)).re := by
  filter_upwards [(isOpen_realDom b R).mem_nhds hz] with y hy
  simp [realHamiltonianExt, indicator_of_mem hy]

/-- Real derivative transport on `EC n k` (the unequal-carrier form of
`KAM.hamiltonian_real_fderiv`). -/
private theorem fderiv_ext_real {V : Set (EC n k)} {H : EC n k → ℂ} {Hr : ER n k → ℝ}
    {z : ER n k} (hV : IsOpen V) (hh : DifferentiableOn ℂ H V)
    (hreal : ∀ y : ER n k, extCx y ∈ V → (H (extCx y)).im = 0)
    (hz : extCx z ∈ V) (hH : ∀ᶠ y in nhds z, Hr y = (H (extCx y)).re) :
    DifferentiableAt ℝ Hr z ∧ ∀ e : ER n k,
      ((fderiv ℝ Hr z e : ℝ) : ℂ) = fderiv ℂ H (extCx z) (extCx e) := by
  set L := extCxCLM n k with hL
  have hz' : L z ∈ V := by rwa [hL, extCxCLM_apply]
  have hhd : DifferentiableAt ℂ H (L z) := hh.differentiableAt (hV.mem_nhds hz')
  have h2 : HasFDerivAt (fun y => H (L y))
      (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L) z :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp z L.hasFDerivAt
  have h3 : HasFDerivAt (fun y => (H (L y)).re)
      (Complex.reCLM.comp (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L)) z :=
    Complex.reCLM.hasFDerivAt.comp z h2
  have hH' : ∀ᶠ y in nhds z, Hr y = (H (L y)).re := by
    simpa only [hL, extCxCLM_apply] using hH
  have h4 : HasFDerivAt Hr (Complex.reCLM.comp
      (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L)) z := h3.congr_of_eventuallyEq hH'
  refine ⟨h4.differentiableAt, fun e => ?_⟩
  have hmem : ∀ᶠ y in nhds z, L y ∈ V := L.continuous.continuousAt.eventually_mem (hV.mem_nhds hz')
  have hev : (fun y => H (L y)) =ᶠ[nhds z] fun y => ((Hr y : ℝ) : ℂ) := by
    filter_upwards [hH', hmem] with y hy hyV
    rw [hy]
    refine Complex.ext (by simp) ?_
    simpa [hL, extCxCLM_apply] using hreal y (by rwa [← extCxCLM_apply])
  have h5 : HasFDerivAt (fun y => ((Hr y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Hr z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h4.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  have := (congrArg (fun L => L e) h6).symm
  simpa [hL, extCxCLM_apply] using this

private theorem extCx_zero_single (j : Fin (n+(k+k))) :
    extCx ((0 : Fin n → ℝ), (Pi.single j 1 : Fin (n+(k+k)) → ℝ)) =
      ((0 : Fin n → ℂ), (Pi.single j 1 : Fin (n+(k+k)) → ℂ)) := by
  ext i <;> simp [extCx, Pi.single_apply, apply_ite Complex.ofReal]

private theorem extCx_single_zero (j : Fin n) :
    extCx ((Pi.single j 1 : Fin n → ℝ), (0 : Fin (n+(k+k)) → ℝ)) =
      ((Pi.single j 1 : Fin n → ℂ), (0 : Fin (n+(k+k)) → ℂ)) := by
  ext i <;> simp [extCx, Pi.single_apply, apply_ite Complex.ofReal]

private theorem realWfield_cx (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hs : 0 < s) (hH : ext_class b R s H) {z : ER n k} (hz : z ∈ b.realDom R) :
    extCx (realWfield b.c (realHamiltonianExt b R H) z) = wfield b.c H (extCx z) := by
  have hzD : extCx z ∈ Dom n b.base R s :=
    (extCx_mem_Dom_iff b hs z).2 ((mem_realDom_iff b R z).1 hz)
  have hd := (fderiv_ext_real (isOpen_Dom (n := n) b.base R s) hH.1.differentiableOn
    (hreal_of_ext hH) hzD (realHamiltonianExt_eventually b R H hz)).2
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · show ((fderiv ℝ (realHamiltonianExt b R H) z (0, Pi.single (Fin.castAdd (k+k) i) 1) : ℝ) : ℂ)
      = fderiv ℂ H (extCx z) (0, Pi.single (Fin.castAdd (k+k) i) 1)
    rw [hd, extCx_zero_single]
  · refine ext_cases (P := fun j => ((((realWfield b.c (realHamiltonianExt b R H) z).2 j : ℝ)) : ℂ)
      = (wfield b.c H (extCx z)).2 j) (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · simp only [realWfield, wfield, Fin.append_left, Complex.ofReal_neg, hd,
        extCx_single_zero]
    · simp only [realWfield, wfield, Fin.append_right, Fin.append_left, Complex.ofReal_mul, hd,
        extCx_zero_single]
    · simp only [realWfield, wfield, Fin.append_right, Complex.ofReal_mul, Complex.ofReal_neg, hd,
        extCx_zero_single]


/-- The componentwise real part `EC n k →L[ℝ] ER n k`. -/
private def extReCLM (n k : ℕ) : EC n k →L[ℝ] ER n k :=
  (ContinuousLinearMap.pi fun i : Fin n => Complex.reCLM.comp (ContinuousLinearMap.proj i)).prodMap
    (ContinuousLinearMap.pi fun i : Fin (n+(k+k)) =>
      Complex.reCLM.comp (ContinuousLinearMap.proj i))

private theorem extReCLM_apply (w : EC n k) : extReCLM n k w = extRe w := rfl

theorem conj (b : PartialBlock n k) {R s r t : ℝ} {H Ht : EC n k → ℂ} {Ψ : EC n k → EC n k}
    (hc : ExtConjHyp b R s r t H Ht Ψ) {J : Set ℝ} {y : ℝ → ER n k}
    (hy : ExtOrbit b r Ht J y) : ExtOrbit b R H J (reExtMap Ψ ∘ y) := by
  intro τ hτ
  obtain ⟨hyτ, hder⟩ := hy τ hτ
  set y0 := y τ with hy0
  have hxD : extCx y0 ∈ Dom n b.base r t :=
    (extCx_mem_Dom_iff b hc.t_pos y0).2 ((mem_realDom_iff b r y0).1 hyτ)
  have hΨx : Ψ (extCx y0) ∈ Dom n b.base R s := hc.maps hxD
  have hre : extCx (reExtMap Ψ y0) = Ψ (extCx y0) := hc.real y0 hxD
  have hmem : reExtMap Ψ y0 ∈ b.realDom R :=
    (mem_realDom_iff b R _).2 (by rw [hre]; exact hΨx.2)
  refine ⟨hmem, ?_⟩
  have hopen : IsOpen (Dom n b.base r t) := isOpen_Dom (n := n) b.base r t
  have hΨd : DifferentiableAt ℂ Ψ (extCx y0) := hc.hol.differentiableAt (hopen.mem_nhds hxD)
  have hHd : DifferentiableAt ℂ H (Ψ (extCx y0)) :=
    hc.outer.1.differentiableOn.differentiableAt
      ((isOpen_Dom (n := n) b.base R s).mem_nhds hΨx)
  -- complex curve
  have hcx : HasDerivAt (fun τ' => extCx (y τ')) (extCx (realWfield b.c
      (realHamiltonianExt b r Ht) y0)) τ := by
    rw [extCx_eq_clm]
    exact (extCxCLM n k).hasFDerivAt.comp_hasDerivAt τ hder
  have hΨcurve : HasDerivAt (fun τ' => Ψ (extCx (y τ')))
      (fderiv ℂ Ψ (extCx y0) (extCx (realWfield b.c (realHamiltonianExt b r Ht) y0))) τ :=
    by
      have h1 := (hΨd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hcx
      exact h1
  -- the value of the derivative
  have hwf : extCx (realWfield b.c (realHamiltonianExt b r Ht) y0) = wfield b.c Ht (extCx y0) :=
    realWfield_cx b hc.t_pos hc.inner hyτ
  have hHt : wfield b.c Ht (extCx y0) = wfield b.c (fun w => H (Ψ w)) (extCx y0) := by
    have hev : Ht =ᶠ[nhds (extCx y0)] fun w => H (Ψ w) := by
      filter_upwards [hopen.mem_nhds hxD] with w hw using hc.identity w hw
    simp only [wfield, hev.fderiv_eq]
  have hfield := symplectic_field hopen hc.hol hc.canon hxD hHd
  have hwR : extCx (realWfield b.c (realHamiltonianExt b R H) (reExtMap Ψ y0)) =
      wfield b.c H (Ψ (extCx y0)) := by
    rw [realWfield_cx b hc.s_pos hc.outer hmem, hre]
  have hcomp : HasDerivAt (fun τ' => extReCLM n k (Ψ (extCx (y τ'))))
      (extReCLM n k (fderiv ℂ Ψ (extCx y0)
        (extCx (realWfield b.c (realHamiltonianExt b r Ht) y0)))) τ :=
    (extReCLM n k).hasFDerivAt.comp_hasDerivAt τ hΨcurve
  show HasDerivAt (fun τ' => reExtMap Ψ (y τ'))
    (realWfield b.c (realHamiltonianExt b R H) (reExtMap Ψ y0)) τ
  refine hcomp.congr_deriv ?_
  rw [hwf, hHt, hfield, ← hwR, extReCLM_apply]
  exact Prod.ext (funext fun i => by simp [extRe, extCx]) (funext fun i => by simp [extRe, extCx])

end Conj

end KAM.Nekhoroshev

end
