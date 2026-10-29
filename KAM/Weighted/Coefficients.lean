/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Norm
public import KAM.Weighted.Parametric
public import KAM.Strip.FourierSeriesVector
public import KAM.Strip.FourierDerivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Coefficients, derivatives and series (`bpN:p4:coefficients`)

For `u` in the class `O(r,s)` (`InClass D r s u`, `0 < s`):

* (a) `coeff_differentiableOn`: `û_k` is holomorphic on `V_r D`
  (`holomorphic_parametric_integral`);
* (b) `coefficients_deriv`: the derivatives `∂_{θⱼ} u`, `∂_{Iᵢ} u` stay in the class and act on the
  coefficients as `2πi kⱼ`, resp. `∂_{Iᵢ}`;
* (c) `coefficients_series`: a series `∑ₖ aₖ(I) χₖ(θ)` with holomorphic coefficients of bounded
  weighted sum lies in the class, with those coefficients and that bound;
* (d) `coefficients_repr`: `u = ∑ₖ û_k χₖ` on `𝒟_{r,s}`, and the one-term bound.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace KAM.Weighted

-- The signatures keep the instance block `[NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W]
-- [FiniteDimensional ℂ W]` (consumers supply it); several lemmas do not need all of it.
set_option linter.unusedSectionVars false

variable {n m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]

/-! ### Real points of the domain -/

/-- A real angle with an action of `V_r D` is a point of `𝒟_{r,s}` for `0 < s`. -/
private theorem realPt_mem_Dom {D : Set (Fin m → ℂ)} {r s : ℝ} (hs : 0 < s) (x : Fin n → ℝ)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) : ((fun j => (x j : ℂ)), I) ∈ Dom n D r s :=
  ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

private theorem continuous_realPt : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-! ### The integrand of the coefficient and its derivative in the actions -/

/-- The unit cube `[0,1]ⁿ`. -/
private abbrev cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

/-- The integrand of `û_k(I)`. -/
private def cG (u : (Fin n → ℂ) × (Fin m → ℂ) → W) (k : Fin n → ℤ) (x : Fin n → ℝ)
    (I : Fin m → ℂ) : W :=
  KAM.character (-k) (fun j => (x j : ℂ)) • u (fun j => (x j : ℂ), I)

private theorem coeff_eq_integral (u : (Fin n → ℂ) × (Fin m → ℂ) → W) (I : Fin m → ℂ)
    (k : Fin n → ℤ) : coeff u I k = ∫ x in cube n, cG u k x I := rfl

private theorem continuous_character_real (k : Fin n → ℤ) :
    Continuous fun x : Fin n → ℝ => KAM.character k (fun j => (x j : ℂ)) :=
  (KAM.differentiable_character k).continuous.comp continuous_realPt

/-- The derivative in the actions of the integrand. -/
private theorem hasFDerivAt_cG {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) (k : Fin n → ℤ) (x : Fin n → ℝ) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) :
    HasFDerivAt (cG u k x)
      (KAM.character (-k) (fun j => (x j : ℂ)) •
        (fderiv ℂ u (fun j => (x j : ℂ), I)).comp
          (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (Fin m → ℂ))) I := by
  have hz : ((fun j => (x j : ℂ)), I) ∈ Dom n D r s := realPt_mem_Dom hs x hI
  have hud : HasFDerivAt u (fderiv ℂ u (fun j => (x j : ℂ), I)) (fun j => (x j : ℂ), I) :=
    (hu.differentiableOn.differentiableAt ((isOpen_Dom D r s).mem_nhds hz)).hasFDerivAt
  exact (hud.comp I (hasFDerivAt_prodMk_right (𝕜 := ℂ) (fun j => (x j : ℂ)) I)).const_smul _

private theorem fderiv_cG {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) (k : Fin n → ℤ) (x : Fin n → ℝ) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) :
    fderiv ℂ (cG u k x) I = KAM.character (-k) (fun j => (x j : ℂ)) •
        (fderiv ℂ u (fun j => (x j : ℂ), I)).comp
          (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (Fin m → ℂ)) :=
  (hasFDerivAt_cG hs hu k x hI).fderiv

/-- The parametric-integral input for the coefficients, `bpN:p4:ext-param` applied to the cube. -/
private theorem coeff_param {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) (k : Fin n → ℤ) :
    DifferentiableOn ℂ (fun I => ∫ x in cube n, cG u k x I) (polyNbhd D r) ∧
      ∀ I ∈ polyNbhd D r, fderiv ℂ (fun I' => ∫ x in cube n, cG u k x I') I =
        ∫ x in cube n, fderiv ℂ (cG u k x) I := by
  have hQ : IsCompact (cube n) := isCompact_univ_pi fun _ => isCompact_Icc
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_Dom (n := n) D r s)
    hu.differentiableOn
  have hmaps : MapsTo (fun y : (Fin n → ℝ) × (Fin m → ℂ) => ((fun j => (y.1 j : ℂ)), y.2))
      (cube n ×ˢ polyNbhd D r) (Dom n D r s) := fun y hy => realPt_mem_Dom hs y.1 hy.2
  have hmapc : Continuous fun y : (Fin n → ℝ) × (Fin m → ℂ) => ((fun j => (y.1 j : ℂ)), y.2) :=
    (continuous_realPt.comp continuous_fst).prodMk continuous_snd
  have hchar : Continuous fun y : (Fin n → ℝ) × (Fin m → ℂ) =>
      KAM.character (-k) (fun j => (y.1 j : ℂ)) :=
    (continuous_character_real (-k)).comp continuous_fst
  refine holomorphic_parametric_integral hQ (isOpen_polyNbhd D r) ?_ ?_ ?_
  · exact hchar.continuousOn.smul
      (hu.differentiableOn.continuousOn.comp hmapc.continuousOn hmaps)
  · intro x _
    have hmI : MapsTo (fun I : Fin m → ℂ => ((fun j => (x j : ℂ)), I)) (polyNbhd D r)
        (Dom n D r s) := fun I hI => realPt_mem_Dom hs x hI
    have hd : DifferentiableOn ℂ (fun I : Fin m → ℂ => u ((fun j => (x j : ℂ)), I))
        (polyNbhd D r) :=
      hu.differentiableOn.comp (differentiableOn_const _ |>.prodMk differentiableOn_id) hmI
    exact hd.const_smul _
  · have hcong : ∀ y ∈ cube n ×ˢ polyNbhd D r, fderiv ℂ (cG u k y.1) y.2 =
        KAM.character (-k) (fun j => (y.1 j : ℂ)) •
          (fderiv ℂ u ((fun j => (y.1 j : ℂ)), y.2)).comp
            (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (Fin m → ℂ)) := fun y hy =>
      fderiv_cG hs hu k y.1 hy.2
    refine ContinuousOn.congr ?_ hcong
    refine hchar.continuousOn.smul ?_
    exact ContinuousOn.clm_comp
      (hreg.1.continuousOn.comp hmapc.continuousOn hmaps) continuousOn_const

/-- (a) `û_k` is holomorphic on `V_r D`. -/
theorem coeff_differentiableOn {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : InClass D r s u) (k : Fin n → ℤ) :
    DifferentiableOn ℂ (fun I => coeff u I k) (polyNbhd D r) :=
  (coeff_param hs hu k).1

/-! ### Derivatives in the class -/

/-- `∂_{θⱼ} u` and `∂_{Iᵢ} u` (Fréchet derivatives in the coordinate directions). -/
def dtheta (j : Fin n) (u : (Fin n → ℂ) × (Fin m → ℂ) → W) : (Fin n → ℂ) × (Fin m → ℂ) → W :=
  fun z => fderiv ℂ u z (Pi.single j 1, 0)

def dI (i : Fin m) (u : (Fin n → ℂ) × (Fin m → ℂ) → W) : (Fin n → ℂ) × (Fin m → ℂ) → W :=
  fun z => fderiv ℂ u z (0, Pi.single i 1)

/-- The series `∑ₖ aₖ(I) χₖ(θ)` of `bpN:p4:coefficients`(c). -/
def fourierSeries (a : (Fin n → ℤ) → (Fin m → ℂ) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, a k z.2 * KAM.character k z.1

private theorem realInclusion_single (i : Fin n) :
    KAM.realInclusion n (Pi.single i 1) = Pi.single i 1 := by
  ext j
  by_cases h : j = i <;> simp [h]

/-- Adding a real angle shift keeps a point of the domain in the domain. -/
private theorem add_single_mem_Dom {D : Set (Fin m → ℂ)} {r s : ℝ} {z : (Fin n → ℂ) × (Fin m → ℂ)}
    (hz : z ∈ Dom n D r s) (j : Fin n) : (z.1 + Pi.single j 1, z.2) ∈ Dom n D r s :=
  ⟨KAM.add_mem_complexStrip_of_im_eq_zero hz.1 fun i => by
    by_cases h : i = j <;> simp [h], hz.2⟩

/-- The derivative of a class function in a fixed direction stays in the class. -/
theorem inClass_fderiv_apply {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hu : InClass D r s u) (v : (Fin n → ℂ) × (Fin m → ℂ)) :
    InClass D r s (fun z => fderiv ℂ u z v) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_Dom (n := n) D r s)
    hu.differentiableOn
  refine ⟨hreg.1.clm_apply (differentiableOn_const v), fun j z hz => ?_⟩
  set a : (Fin n → ℂ) × (Fin m → ℂ) := (Pi.single j 1, 0) with ha
  have hza : (z.1 + Pi.single j 1, z.2) = z + a := by
    ext <;> simp [ha]
  have hev : (fun w => u (w + a)) =ᶠ[𝓝 z] u := by
    filter_upwards [(isOpen_Dom (n := n) D r s).mem_nhds hz] with w hw
    have := hu.periodic j w hw
    rw [← this]
    congr 1
    ext <;> simp [ha]
  have h1 : fderiv ℂ u (z + a) = fderiv ℂ u z := by
    rw [← fderiv_comp_add_right (f := u) (x := z) a]
    exact hev.fderiv_eq
  show fderiv ℂ u (z.1 + Pi.single j 1, z.2) v = fderiv ℂ u z v
  rw [hza, h1]

/-- Along the real angles the class function is continuous. -/
private theorem continuous_real_restrict {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : DifferentiableOn ℂ u (Dom n D r s))
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) :
    Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
  hu.continuousOn.comp_continuous (continuous_realPt.prodMk continuous_const)
    fun x => realPt_mem_Dom hs x hI

private theorem continuous_fderiv_real {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : DifferentiableOn ℂ u (Dom n D r s))
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) :
    Continuous fun x : Fin n → ℝ => fderiv ℂ u (fun j => (x j : ℂ), I) :=
  (KAM.holomorphic_regularity_of_finiteDimensional (isOpen_Dom (n := n) D r s)
    hu).1.continuousOn.comp_continuous
    (continuous_realPt.prodMk continuous_const) fun x => realPt_mem_Dom hs x hI

/-- The real derivative of `x ↦ φ (u (x, I))` is `φ` of the complex derivative. -/
private theorem hasFDerivAt_real_restrict {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : DifferentiableOn ℂ u (Dom n D r s))
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (φ : W →L[ℂ] ℂ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => φ (u (fun j => (y j : ℂ), I)))
      ((φ.restrictScalars ℝ).comp (((fderiv ℂ u (fun j => (x j : ℂ), I)).restrictScalars ℝ).comp
        ((KAM.realInclusion n).prod 0))) x := by
  have hz : ((fun j => (x j : ℂ)), I) ∈ Dom n D r s := realPt_mem_Dom hs x hI
  have hud : HasFDerivAt u (fderiv ℂ u (fun j => (x j : ℂ), I)) (fun j => (x j : ℂ), I) :=
    (hu.differentiableAt ((isOpen_Dom D r s).mem_nhds hz)).hasFDerivAt
  have hg : HasFDerivAt (fun y : Fin n → ℝ => ((fun j => (y j : ℂ)), I))
      ((KAM.realInclusion n).prod 0) x :=
    (KAM.realInclusion n).hasFDerivAt.prodMk (hasFDerivAt_const I x)
  exact (φ.restrictScalars ℝ).hasFDerivAt.comp x ((hud.restrictScalars ℝ).comp x hg)

/-- `x ↦ φ (u (x, I))` is `C¹` and `1`-periodic on `ℝⁿ`. -/
private theorem contDiff_real_restrict {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : InClass D r s u)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (φ : W →L[ℂ] ℂ) :
    ContDiff ℝ 1 fun y : Fin n → ℝ => φ (u (fun j => (y j : ℂ), I)) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional (isOpen_Dom (n := n) D r s)
    hu.differentiableOn
  have h1 : ContDiffOn ℝ 1 u (Dom n D r s) :=
    (hreg.2.2.1.restrict_scalars ℝ).of_le (by exact_mod_cast le_top)
  have hg : ContDiff ℝ 1 fun y : Fin n → ℝ => ((fun j => (y j : ℂ)), I) :=
    ((KAM.realInclusion n).contDiff).prodMk contDiff_const
  have h2 : ContDiffOn ℝ 1 (u ∘ fun y : Fin n → ℝ => ((fun j => (y j : ℂ)), I)) univ :=
    h1.comp hg.contDiffOn fun y _ => realPt_mem_Dom hs y hI
  exact (φ.restrictScalars ℝ).contDiff.comp (contDiffOn_univ.1 h2)

/-- The coefficients of `∂_{θⱼ} u` are `2πi kⱼ û_k` (integration by parts over the real torus, by
duality from `KAM.torusCoeff_fderiv_coordinate_real`). -/
private theorem coeff_dtheta {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) (j : Fin n) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r)
    (k : Fin n → ℤ) :
    coeff (dtheta j u) I k = (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) • coeff u I k := by
  have hdu : InClass D r s (dtheta j u) := inClass_fderiv_apply hu _
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun φ => ?_
  have hc0 := continuous_real_restrict hs hu.differentiableOn hI
  have hc1 := continuous_real_restrict hs hdu.differentiableOn hI
  unfold coeff
  rw [KAM.clm_torusCoeffW hc1 φ k, map_smul, KAM.clm_torusCoeffW hc0 φ k, smul_eq_mul]
  have hp : ∀ (i : Fin n) (x : Fin n → ℝ), (fun y : Fin n → ℝ => φ (u (fun j => (y j : ℂ), I)))
      (x + Pi.single i 1) = φ (u (fun j => (x j : ℂ), I)) := by
    intro i x
    have hshift : (fun j => ((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℂ)) =
        (fun j => (x j : ℂ)) + Pi.single i 1 := by
      have := map_add (KAM.realInclusion n) x (Pi.single i 1)
      rw [realInclusion_single] at this
      exact this
    show φ (u (fun j => ((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℂ), I)) = _
    rw [hshift]
    exact congrArg φ (hu.periodic i _ (realPt_mem_Dom hs x hI))
  have key := KAM.torusCoeff_fderiv_coordinate_real (contDiff_real_restrict hs hu hI φ) hp j k
  rw [← key]
  congr 1
  funext x
  rw [(hasFDerivAt_real_restrict hs hu.differentiableOn hI φ x).fderiv]
  simp [dtheta, realInclusion_single]

/-- The coefficients of `∂_{Iᵢ} u` are the derivatives of the coefficients (differentiation under
the integral, `bpN:p4:ext-param`). -/
private theorem coeff_dI {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) (i : Fin m) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r)
    (k : Fin n → ℤ) :
    coeff (dI i u) I k = fderiv ℂ (fun I' => coeff u I' k) I (Pi.single i 1) := by
  have hcont : Continuous fun x : Fin n → ℝ => fderiv ℂ (cG u k x) I := by
    have hfun : (fun x : Fin n → ℝ => fderiv ℂ (cG u k x) I) = fun x =>
        KAM.character (-k) (fun j => (x j : ℂ)) •
          (fderiv ℂ u (fun j => (x j : ℂ), I)).comp
            (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (Fin m → ℂ)) :=
      funext fun x => fderiv_cG hs hu k x hI
    rw [hfun]
    exact (continuous_character_real (-k)).smul
      ((continuous_fderiv_real hs hu.differentiableOn hI).clm_comp continuous_const)
  have hint : Integrable (fun x : Fin n → ℝ => fderiv ℂ (cG u k x) I) (volume.restrict (cube n)) :=
    KAM.integrableOn_unitCube_of_continuous hcont
  have h1 : fderiv ℂ (fun I' => coeff u I' k) I = ∫ x in cube n, fderiv ℂ (cG u k x) I :=
    (coeff_param hs hu k).2 I hI
  rw [h1, ContinuousLinearMap.integral_apply hint]
  show ∫ x in cube n, cG (dI i u) k x I = _
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [cG, dI, fderiv_cG hs hu k x hI]

/-- (b) derivatives stay in the class and act on coefficients as `2πi kⱼ` resp. `∂_{Iᵢ}`. -/
theorem coefficients_deriv {D : Set (Fin m → ℂ)} {r s : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) :
    (∀ j : Fin n, InClass D r s (dtheta j u) ∧ ∀ I ∈ polyNbhd D r, ∀ k,
      coeff (dtheta j u) I k = (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) • coeff u I k) ∧
    (∀ i : Fin m, InClass D r s (dI i u) ∧ ∀ I ∈ polyNbhd D r, ∀ k,
      coeff (dI i u) I k = fderiv ℂ (fun I' => coeff u I' k) I (Pi.single i 1)) :=
  ⟨fun j => ⟨inClass_fderiv_apply hu _, fun _ hI k => coeff_dtheta hs hu j hI k⟩,
    fun i => ⟨inClass_fderiv_apply hu _, fun _ hI k => coeff_dI hs hu i hI k⟩⟩

/-! ### Series with holomorphic coefficients -/

/-- The terms of the series are holomorphic on the domain. -/
private theorem differentiableOn_series_term {D : Set (Fin m → ℂ)} {r s : ℝ}
    {a : (Fin n → ℤ) → (Fin m → ℂ) → ℂ} (ha : ∀ k, DifferentiableOn ℂ (a k) (polyNbhd D r))
    (k : Fin n → ℤ) :
    DifferentiableOn ℂ (fun z : (Fin n → ℂ) × (Fin m → ℂ) => a k z.2 * KAM.character k z.1)
      (Dom n D r s) :=
  ((ha k).comp differentiableOn_snd fun _ hz => hz.2).mul
    (((KAM.differentiable_character k).comp differentiable_fst).differentiableOn)

/-- Weierstrass M-test for the series. -/
private theorem series_tendstoUniformlyOn {D : Set (Fin m → ℂ)} {r s S : ℝ}
    {a : (Fin n → ℤ) → (Fin m → ℂ) → ℂ}
    (hterm : ∀ I ∈ polyNbhd D r, ∀ k, ‖a k I‖ * modeWeight s k ≤ S) {s' : ℝ} (hs' : s' < s) :
    TendstoUniformlyOn
      (fun (Λ : Finset (Fin n → ℤ)) (z : (Fin n → ℂ) × (Fin m → ℂ)) =>
        ∑ k ∈ Λ, a k z.2 * KAM.character k z.1)
      (fourierSeries a) Filter.atTop (Dom n D r s') := by
  have hx : 0 < 2 * Real.pi * (s - s') := by
    have := Real.pi_pos
    have : 0 < s - s' := by linarith
    positivity
  refine tendstoUniformlyOn_tsum
    (u := fun k : Fin n → ℤ => S * Real.exp (-(2 * Real.pi * (s - s')) * KAM.Fourier.modeSize k))
    ((KAM.Fourier.hasSum_exp_neg_modeSize n hx).summable.mul_left S) ?_
  intro k z hz
  rw [norm_mul]
  have h1 := KAM.norm_character_le k hz.1
  have h2 := hterm z.2 hz.2 k
  have he : modeWeight s k * Real.exp (-(2 * Real.pi * (s - s')) * KAM.Fourier.modeSize k) =
      Real.exp (2 * Real.pi * s' * KAM.Fourier.modeSize k) := by
    rw [modeWeight, ← Real.exp_add]
    congr 1
    ring
  calc ‖a k z.2‖ * ‖KAM.character k z.1‖
      ≤ ‖a k z.2‖ * Real.exp (2 * Real.pi * s' * KAM.Fourier.modeSize k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖a k z.2‖ * modeWeight s k) *
          Real.exp (-(2 * Real.pi * (s - s')) * KAM.Fourier.modeSize k) := by
        rw [mul_assoc ‖a k z.2‖ (modeWeight s k), he]
    _ ≤ S * Real.exp (-(2 * Real.pi * (s - s')) * KAM.Fourier.modeSize k) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- The coefficients of the series are the `a k`. -/
private theorem coeff_fourierSeries {s : ℝ}
    {a : (Fin n → ℤ) → (Fin m → ℂ) → ℂ} (hs : 0 < s) {I : Fin m → ℂ}
    (hI : Summable fun k => ‖a k I‖ * modeWeight s k) (k : Fin n → ℤ) :
    coeff (fourierSeries a) I k = a k I :=
  KAM.torusCoeff_fourierSum (a := fun l => a l I) hs.le hI k

/-- (c) series with holomorphic coefficients of finite weighted sum. -/
theorem coefficients_series {D : Set (Fin m → ℂ)} {r s S : ℝ} {a : (Fin n → ℤ) → (Fin m → ℂ) → ℂ}
    (hs : 0 < s) (ha : ∀ k, DifferentiableOn ℂ (a k) (polyNbhd D r))
    (hS : ∀ I ∈ polyNbhd D r, Summable (fun k => ‖a k I‖ * modeWeight s k) ∧
      ∑' k, ‖a k I‖ * modeWeight s k ≤ S) :
    (∀ s' < s, TendstoUniformlyOn
      (fun (Λ : Finset (Fin n → ℤ)) z => ∑ k ∈ Λ, a k z.2 * KAM.character k z.1)
      (fourierSeries a) Filter.atTop (Dom n D r s')) ∧
    InClass D r s (fourierSeries a) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, coeff (fourierSeries a) I k = a k I) ∧
    WBound D r s (fourierSeries a) S := by
  have hterm : ∀ I ∈ polyNbhd D r, ∀ k, ‖a k I‖ * modeWeight s k ≤ S := fun I hI k =>
    ((hS I hI).1.le_tsum k fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans
      (hS I hI).2
  have hconv : ∀ s' < s, TendstoUniformlyOn
      (fun (Λ : Finset (Fin n → ℤ)) (z : (Fin n → ℂ) × (Fin m → ℂ)) =>
        ∑ k ∈ Λ, a k z.2 * KAM.character k z.1)
      (fourierSeries a) Filter.atTop (Dom n D r s') := fun s' hs' =>
    series_tendstoUniformlyOn hterm hs'
  have hdiff : DifferentiableOn ℂ (fourierSeries a) (Dom n D r s) := by
    intro z hz
    obtain ⟨ε, hε, hzε⟩ := KAM.exists_mem_complexStrip_sub hz.1
    have hz' : z ∈ Dom n D r (s - ε) := ⟨hzε, hz.2⟩
    have hK : ∀ N : ℕ, DifferentiableOn ℂ
        (fun z : (Fin n → ℂ) × (Fin m → ℂ) => ∑ k ∈ KAM.modeCutoff n N,
          a k z.2 * KAM.character k z.1) (Dom n D r (s - ε)) := fun N =>
      DifferentiableOn.fun_sum fun k _ => differentiableOn_series_term ha k
    have hconvN : TendstoUniformlyOn
        (fun (N : ℕ) (z : (Fin n → ℂ) × (Fin m → ℂ)) => ∑ k ∈ KAM.modeCutoff n N,
          a k z.2 * KAM.character k z.1) (fourierSeries a) Filter.atTop (Dom n D r (s - ε)) :=
      fun v hv => (KAM.tendsto_modeCutoff n).eventually (hconv (s - ε) (by linarith) v hv)
    exact ((uniform_limit_holomorphic (isOpen_Dom D r (s - ε)) hK hconvN).1.differentiableAt
      ((isOpen_Dom D r (s - ε)).mem_nhds hz')).differentiableWithinAt
  have hper : ∀ j : Fin n, ∀ z ∈ Dom n D r s,
      fourierSeries a (z.1 + Pi.single j 1, z.2) = fourierSeries a z := fun j z _ => by
    simp only [fourierSeries, KAM.character_add_single]
  have hcoeff : ∀ I ∈ polyNbhd D r, ∀ k, coeff (fourierSeries a) I k = a k I :=
    fun I hI k => coeff_fourierSeries hs (hS I hI).1 k
  refine ⟨hconv, ⟨hdiff, hper⟩, hcoeff, fun I hI => ?_⟩
  have hfun : (fun k => ‖coeff (fourierSeries a) I k‖ * modeWeight s k) =
      fun k => ‖a k I‖ * modeWeight s k := funext fun k => by rw [hcoeff I hI k]
  exact ⟨by unfold WSummable; rw [hfun]; exact (hS I hI).1,
    by unfold wsum; rw [hfun]; exact (hS I hI).2⟩

/-! ### The Fourier representation -/

/-- At fixed `I`, a class function equals the Fourier series of its coefficients on the strip
(no boundedness is needed: the coefficient series converges at radius `s`). -/
private theorem eq_fourierSumVec_coeff {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → W} (hs : 0 < s) (hu : InClass D r s u)
    {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r)
    (ha : Summable fun k : Fin n → ℤ => ‖coeff u I k‖ * modeWeight s k)
    {θ : Fin n → ℂ} (hθ : θ ∈ KAM.complexStrip n s) :
    u (θ, I) = KAM.fourierSumVec (coeff u I) θ := by
  obtain ⟨-, -, -, hdiff, hper, hcoef⟩ := KAM.summation_forward_vec hs.le ha
  have hmaps : MapsTo (fun θ : Fin n → ℂ => (θ, I)) (KAM.complexStrip n s) (Dom n D r s) :=
    fun θ hθ => ⟨hθ, hI⟩
  have hud : DifferentiableOn ℂ (fun θ : Fin n → ℂ => u (θ, I)) (KAM.complexStrip n s) :=
    hu.differentiableOn.comp (differentiableOn_id.prodMk (differentiableOn_const I)) hmaps
  have hc0 := continuous_real_restrict hs hu.differentiableOn hI
  have hc1 : Continuous fun x : Fin n → ℝ => KAM.fourierSumVec (coeff u I) fun j => (x j : ℂ) :=
    hdiff.continuousOn.comp_continuous continuous_realPt (KAM.ofReal_mem_complexStrip hs)
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun φ => ?_
  have hg := KAM.eq_zero_of_torusCoeff_holomorphic hs
    (v := fun θ => φ (u (θ, I)) - φ (KAM.fourierSumVec (coeff u I) θ))
    ((φ.differentiable.comp_differentiableOn hud).sub
      (φ.differentiable.comp_differentiableOn hdiff))
    (fun i z hz => by
      show φ (u (z + Pi.single i 1, I)) - φ (KAM.fourierSumVec (coeff u I) (z + Pi.single i 1)) =
        φ (u (z, I)) - φ (KAM.fourierSumVec (coeff u I) z)
      rw [hu.periodic i (z, I) ⟨hz, hI⟩, hper i z hz])
    (fun k => by
      show KAM.torusCoeff (fun x => φ (u (fun j => (x j : ℂ), I)) -
        φ (KAM.fourierSumVec (coeff u I) fun j => (x j : ℂ))) k = 0
      rw [KAM.torusCoeff_sub (f := fun x => φ (u (fun j => (x j : ℂ), I)))
        (g := fun x => φ (KAM.fourierSumVec (coeff u I) fun j => (x j : ℂ)))
        (φ.continuous.comp hc0) (φ.continuous.comp hc1) k,
        ← KAM.clm_torusCoeffW hc0 φ k, ← KAM.clm_torusCoeffW hc1 φ k, hcoef k]
      exact sub_self _) θ hθ
  exact sub_eq_zero.mp hg

/-- (d) Fourier representation `u = ∑ₖ û_k χₖ` on `𝒟_{r,s}`, and the one-term bound. -/
theorem coefficients_repr {D : Set (Fin m → ℂ)} {r s M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → W}
    (hs : 0 < s) (hu : InClass D r s u) (hb : WBound D r s u M) :
    (∀ z ∈ Dom n D r s, HasSum (fun k => KAM.character k z.1 • coeff u z.2 k) (u z)) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, ‖coeff u I k‖ * modeWeight s k ≤ M) := by
  refine ⟨fun z hz => ?_, fun I hI k => ?_⟩
  · have ha : Summable fun k : Fin n → ℤ => ‖coeff u z.2 k‖ * modeWeight s k := (hb z.2 hz.2).1
    have hsum := KAM.summable_character_smul ha hz.1
    have heq := eq_fourierSumVec_coeff hs hu hz.2 ha hz.1
    have : u z = KAM.fourierSumVec (coeff u z.2) z.1 := heq
    rw [this]
    exact hsum.hasSum
  · exact ((hb I hI).1.le_tsum k fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans
      (hb I hI).2

end KAM.Weighted

end
